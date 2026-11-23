import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperUnitriangularMul

noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedFrames

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem exists_coef_of_mem_span_image {V : Type*} [AddCommGroup V] [Module E V] (e : Fin r → V)
    (s : Set (Fin r)) {x : V} (hx : x ∈ Submodule.span E (e '' s)) :
    ∃ l : Fin r → E, (∀ k, k ∉ s → l k = 0) ∧ x = ∑ k, l k • e k := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, fun k hk => ?_, ?_⟩
  · by_contra h; exact hk (hl (Finsupp.mem_support_iff.mpr h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]; intro i; simp

theorem z_mem_orth (F : FlagG S r T) : F.z ∈ orth S (Submodule.span E (Set.range F.e)) := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.z_orth a
  | zero => simp
  | add a b _ _ ha hb => simp [map_add, ha, hb]
  | smul c a _ ha => simp [ha]

theorem exists_upUni (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V)
    (h1 : ∀ j, ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j)
    (h2 : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, b < a → W a b = 0) ∧ (∀ a, W a a = 1) ∧
      ∀ b, n (frame F b) = ∑ a, W a b • frame F a := by
  have key : ∀ b : Fin (r + 1), ∃ l : Fin r → E, (∀ k, b ≤ Fin.castSucc k → l k = 0) ∧
      n (frame F b) = frame F b + ∑ k, l k • F.fl.e k := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      have hz : frame F (Fin.last r) = F.fl.z := by simp [frame, FlagG.fvec]
      have hm := h2 _ (z_mem_orth F.fl)
      have hm' : n F.fl.z - F.fl.z ∈ Submodule.span E (F.fl.e '' Set.univ) := by
        rw [Set.image_univ]; exact hm
      obtain ⟨l, -, hl⟩ := exists_coef_of_mem_span_image F.fl.e Set.univ hm'
      refine ⟨l, fun k hk => absurd hk (not_le.mpr (Fin.castSucc_lt_last k)), ?_⟩
      rw [hz, ← hl]; abel
    | cast i =>
      have hf : frame F (Fin.castSucc i) = F.fl.e i := by simp [frame, FlagG.fvec]
      have hmem : F.fl.e i ∈ Xflag F (i.val + 1) :=
        Submodule.subset_span (Set.mem_image_of_mem _ (show i ∈ {k : Fin r | k.1 < i.1 + 1} from Nat.lt_succ_self _))
      have hm : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1}) := by
        have := h1 i.val _ hmem
        rw [hf] at *
        exact this
      obtain ⟨l, hl0, hl⟩ := exists_coef_of_mem_span_image F.fl.e _ hm
      refine ⟨l, fun k hk => hl0 k ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, not_lt]; exact Fin.castSucc_le_castSucc_iff.mp hk
      · rw [hf, ← hl]; abel
  choose l hl0 hl using key
  refine ⟨Matrix.of fun a b => Fin.snoc (α := fun _ => E) (l b) 0 a + if a = b then 1 else 0, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [Matrix.of_apply, if_neg (ne_of_gt hab), add_zero]
    induction a using Fin.lastCases with
    | last => simp
    | cast k => simp only [Fin.snoc_castSucc]; exact hl0 b k hab.le
  · intro a
    simp only [Matrix.of_apply, if_pos rfl]
    induction a using Fin.lastCases with
    | last => simp
    | cast k => simp only [Fin.snoc_castSucc]; rw [hl0 _ k le_rfl]; simp
  · intro b
    rw [hl b]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp [frame, FlagG.fvec, add_comm]

theorem upUni_mul {N : ℕ} {U W : Matrix (Fin N) (Fin N) E} (hU0 : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) (hW0 : ∀ a b, b < a → W a b = 0) (hW1 : ∀ a, W a a = 1) :
    (∀ a b, b < a → (U * W) a b = 0) ∧ (∀ a, (U * W) a a = 1) := by
  first
  | exact @_root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
  | exact _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
  | (apply _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul ..)

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (b : Fin (r + 1)) :
    frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF
  rw [dif_pos hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast k => simp [frame, FlagG.fvec, mapFlag]

end Gen

end GlobalTheory.MovedFrames

namespace GlobalTheory.MovedFrames

theorem map_sum_frame {E V : Type*} [Field E] [AddCommGroup V] [Module E V] {N : ℕ} (ρ : V ≃ₗ[E] V)
    (U W : Matrix (Fin N) (Fin N) E) (f g : Fin N → V) (hF : ∀ a, ρ (f a) = ∑ c, U c a • g c) (b : Fin N) :
    ρ (∑ a, W a b • f a) = ∑ c, (U * W) c b • g c := by
  rw [map_sum]
  simp only [map_smul, hF, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

end GlobalTheory.MovedFrames

namespace GlobalTheory.MovedFrames

theorem moved_frames : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → ∃ B B' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧ (∀ a b, b < a → B' a b = 0) ∧ (∀ a, B' a a = 1) ∧ ∀ b, ρ (n (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • frame F00 a ∧ ρ (n (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • frame F'0 a := by
  intro D X Y u u' F00 F'0 t₀ ρ U U' hM n m hn hm
  obtain ⟨_, hU, hU', hF, hF'⟩ := hM
  obtain ⟨W, hW0, hW1, hWe⟩ := exists_upUni _ n hn.2.1 hn.2.2
  obtain ⟨W', hW'0, hW'1, hW'e⟩ := exists_upUni _ m hm.2.1 hm.2.2
  have hlin : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem (inv_mem hn.1) hlin) hm.1
  obtain ⟨hB0, hB1⟩ := upUni_mul (fun a b h => (hU a b).1 h) (fun a => (hU a a).2 rfl) hW0 hW1
  obtain ⟨hB'0, hB'1⟩ := upUni_mul (fun a b h => (hU' a b).1 h) (fun a => (hU' a a).2 rfl) hW'0 hW'1
  refine ⟨U * W, U' * W', hB0, hB1, hB'0, hB'1, fun b => ⟨?_, ?_⟩⟩
  · rw [hWe]
    exact map_sum_frame ρ U W _ _ hF b
  · have ht : ∀ a, t₀.lin (frame (lf D (X.Fu u')) a) = frame t₀.frame a := fun a => by
      rw [← frame_mapLF _ hlin]; rfl
    have hx : ∀ x, n ((n⁻¹ * t₀.lin * m) x) = t₀.lin (m x) := fun x => by
      rw [← LinearEquiv.mul_apply, show n * (n⁻¹ * t₀.lin * m) = t₀.lin * m by group,
        LinearEquiv.mul_apply]
    have hF2 : ∀ a, (t₀.lin.trans ρ) (frame (lf D (X.Fu u')) a) = ∑ c, U' c a • frame F'0 c := by
      intro a
      rw [LinearEquiv.trans_apply, ht, hF']
    rw [frame_mapLF _ hγ, hx, hW'e]
    have := map_sum_frame (t₀.lin.trans ρ) U' W' _ _ hF2 b
    rw [← this, LinearEquiv.trans_apply, map_sum]

end GlobalTheory.MovedFrames
