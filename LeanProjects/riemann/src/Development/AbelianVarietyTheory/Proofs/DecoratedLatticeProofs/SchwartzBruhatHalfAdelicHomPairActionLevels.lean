import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Formalism.LocalToGlobal.Columns.RecLevelLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsKeepStandardLattice
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.SBMove

open Formalism.L2.Col in

theorem isFrame_one_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (n : ℕ) : Formalism.L2.DIV.IsFrame (F := F) 1 (Formalism.L2.Col.stdLat E n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro x
    simp only [inv_one, Units.val_one, Matrix.one_mulVec, IsEmpty.forall_iff, iff_true]
    rw [Subsingleton.elim x 0]; exact zero_mem _
  · haveI : NeZero n := ⟨hn.ne'⟩
    have e : Formalism.L2.Col.stdLat E n = baseLb E n ∅ := by
      ext x
      rw [rll_mem_baseLb]
      constructor
      · intro h
        have h' : ∀ j, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x j := fun j =>
          (Submodule.mem_one).1 ((Submodule.mem_pi).1 h j (Set.mem_univ _))
        choose r hr using h'
        exact ⟨r, hr, fun P hP => absurd hP (Finset.notMem_empty _)⟩
      · rintro ⟨r, hr, -⟩
        exact (Submodule.mem_pi).2 fun j _ => (Submodule.mem_one).2 ⟨r j, hr j⟩
    intro x
    rw [e, rll_mem_hat_base, inv_one, Units.val_one, Matrix.one_mulVec]
    constructor
    · rintro ⟨y, hy, -⟩ i
      exact hy i ▸ (y i).2
    · exact fun h => ⟨fun i => ⟨x i, h i⟩, fun _ => rfl, fun P hP => absurd hP (Finset.notMem_empty _)⟩

theorem mulVec_mem_sub {A : Type} [CommRing A] {n : ℕ} (R : Subring A) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ a b, M a b ∈ R) (v : Fin n → A) (hv : ∀ i, v i ∈ R) (i : Fin n) : (M *ᵥ v) i ∈ R := by
  simp only [Matrix.mulVec, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hM i j) (hv j)

theorem isFrame_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} (hL : Formalism.L2.DIV.IsFrame (F := F) 1 L)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (h1 : ∀ a b, (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ a b, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b ∈
      Formalism.L2.Herm.intAf F E) : Formalism.L2.DIV.IsFrame β L := by
  intro x
  rw [hL x, inv_one, Units.val_one, Matrix.one_mulVec]
  constructor
  · intro hx i; exact mulVec_mem_sub _ _ h2 x hx i
  · intro hx i
    have e : x = (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]; exact mulVec_mem_sub _ _ h1 _ hx i

theorem int_of_moves {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (h : Moves V hn g (Formalism.L2.Col.stdLat D.host.E n)) (a b : Fin V.rank) :
    toEAf D (Formalism.L2.Theta.mt V g⁻¹ a b) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hmem : (Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) ∈ Formalism.L2.Col.stdLat D.host.E n := by
    refine (Submodule.mem_pi).2 fun j _ => ?_
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp only [Pi.single_eq_same]; exact Submodule.one_le.1 le_rfl
    · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
  have h' := (h _).1 hmem (Fin.cast hn a)
  have e : (fun j => eToEAf D ((Pi.single (Fin.cast hn b) 1 : Fin n → D.host.E) j)) =
      Pi.single (Fin.cast hn b) 1 := by
    funext j
    by_cases hj : j = Fin.cast hn b
    · subst hj; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [e, Matrix.mulVec_single_one] at h'
  simpa [finM, Matrix.reindex_apply] using h'

end GlobalTheory.SBMove

namespace GlobalTheory.SBMove

theorem mt_mul_inv_eq {D : D7} (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  simp only [Formalism.L2.Theta.mt]
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  simp only [actO, inv_inv]
  simp only [← Matrix.mul_assoc]
  rw [mt_mul_inv_eq, Matrix.one_mul, Matrix.mul_assoc, mt_mul_inv_eq, Matrix.mul_one]

theorem actO_add' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  simp only [actO, Matrix.mul_add, Matrix.add_mul]

theorem actO_zero' {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) :
    actO S T g h 0 = 0 := by
  simp only [actO, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (y : WO S T) (k : ℕ) :
    actO S T g h (k • y) = k • actO S T g h y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, actO_zero']
  | succ k ih => rw [succ_nsmul, succ_nsmul, actO_add', ih]

theorem actO_add_nsmul {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x y : WO S T) (k : ℕ) :
    actO S T g h (x + k • y) = actO S T g h x + k • actO S T g h y := by
  rw [actO_add', actO_nsmul]

theorem actO_isHalf {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : x = e • x := by
    ext a b; exact (hx a b).symm
  have key : actO S T g h x = e • actO S T g h x := by
    conv_lhs => rw [hx']
    simp only [actO, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  have := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem coe_stdLat {D : D7} (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, intVec, Set.mem_setOf_eq]
  rw [Formalism.L2.Col.stdLat, Submodule.mem_pi]
  refine forall_congr' fun k => ?_
  simp only [Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · rintro ⟨y, hy⟩; rw [← hy]; exact y.isIntegral_coe
  · intro hk; exact ⟨⟨x k, hk⟩, rfl⟩

theorem actO_mem_stdHom {D : D7} (S T : HSp D) {n m : ℕ} (hn : S.rank = n) (hm : T.rank = m) (g : GA D S) (h : GA D T)
    (hg : Moves S hn g (Formalism.L2.Col.stdLat D.host.E n)) (hg' : Moves S hn g⁻¹ (Formalism.L2.Col.stdLat D.host.E n))
    (hh : Moves T hm h (Formalism.L2.Col.stdLat D.host.E m)) (hh' : Moves T hm h⁻¹ (Formalism.L2.Col.stdLat D.host.E m))
    {x : WO S T} (hx : x ∈ stdHom S T) : actO S T g h x ∈ stdHom S T := by
  have e : stdHom S T = latO S T ((Formalism.L2.Col.stdLat D.host.E S.rank : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) : Set (Fin S.rank → D.host.E))
      ((Formalism.L2.Col.stdLat D.host.E T.rank : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) fun _ => True := by
    rw [coe_stdLat, coe_stdLat]
  rw [e] at hx ⊢
  have fr : ∀ (V : HSp D) {k : ℕ} (hk : V.rank = k) (b : GA D V), Moves V hk b (Formalism.L2.Col.stdLat D.host.E k) →
      Moves V hk b⁻¹ (Formalism.L2.Col.stdLat D.host.E k) →
      Formalism.L2.DIV.IsFrame (Matrix.GeneralLinearGroup.map (toEAf D) (matHom V b)) (Formalism.L2.Col.stdLat D.host.E V.rank) := by
    intro V k hk b hb hb'
    refine isFrame_of_int (isFrame_one_std _) _ (fun a c => ?_) (fun a c => ?_)
    · have := int_of_moves V hk b⁻¹ hb' a c
      rw [inv_inv] at this
      exact this
    · rw [← map_inv, ← map_inv]
      exact int_of_moves V hk b hb a c
  exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g h _ _ _ _ 1 (Matrix.GeneralLinearGroup.map (toEAf D) (matHom S g)) 1
    (Matrix.GeneralLinearGroup.map (toEAf D) (matHom T h)) (isFrame_one_std _) (fr S hn g hg hg') (isFrame_one_std _)
    (fr T hm h hh hh') (by rw [Units.val_one, Matrix.mul_one]; rfl) (by rw [Units.val_one, Matrix.mul_one]; rfl) x hx

end GlobalTheory.SBMove

open GlobalTheory.SBMove in

theorem GlobalTheory.SBMove.isSBHalf_actO_lev : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  intro B X I hI hP l Z u a Ch A hA i hi α γ Φ hΦ κ κ'
  have hi0 : i ≤ B.R.m := Nat.le_of_succ_le hi
  have hU : ∀ j (hj : j ≤ B.R.m) (β : Ch j) g, g ∈ A.U j β →
      Moves _ (rankN (I.rec7 l Z) j hj) g (Formalism.L2.Col.stdLat B.fields.E _) :=
    fun j hj β g hg => GlobalTheory.AdForm.levels_keep_stdLat I hI hP l Z u a Ch A hA j hj β g hg
  have hG : ∀ x ∈ stdHom _ _, actO _ _ κ.1⁻¹ κ'.1⁻¹ x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ (inv_mem κ.2)) (hU i hi0 α _ (by rw [inv_inv]; exact κ.2))
      (hU (i + 1) hi γ _ (inv_mem κ'.2)) (hU (i + 1) hi γ _ (by rw [inv_inv]; exact κ'.2)) hx
  have hH : ∀ x ∈ stdHom _ _, actO _ _ κ.1 κ'.1 x ∈ stdHom _ _ := fun x hx =>
    actO_mem_stdHom _ _ _ _ _ _ (hU i hi0 α _ κ.2) (hU i hi0 α _ (inv_mem κ.2))
      (hU (i + 1) hi γ _ κ'.2) (hU (i + 1) hi γ _ (inv_mem κ'.2)) hx
  obtain ⟨hsupp, k, hk, hinv, hden⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun v hv hve t => ?_, fun t ht => ?_⟩
  · rw [← actO_actO_inv κ.1 κ'.1 t]
    exact actO_isHalf _ _ _ (hsupp _ ht)
  · show Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (t + k • v)) = Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ t)
    rw [actO_add_nsmul]
    exact hinv _ (hG v hv) (actO_isHalf _ _ _ hve) _
  · have h1 := hden _ ht
    rw [← actO_nsmul] at h1
    rw [← actO_actO_inv κ.1 κ'.1 (k • t)]
    exact hH _ h1
