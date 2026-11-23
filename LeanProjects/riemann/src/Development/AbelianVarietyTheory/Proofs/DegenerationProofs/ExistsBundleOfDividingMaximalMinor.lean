import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanEqSpanMinor
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open Matrix GlobalTheory.ZH.DualLattice

noncomputable section
namespace GlobalTheory.ZH.MinorBundle

section Algebra

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type} [Fintype J] [DecidableEq J]

theorem dual_dual {G L : Matrix J J Ω} {t : Ω} (ht : t ≠ 0) (hL : L.det ≠ 0)
    (h : Submodule.span S (Set.range (t⁻¹ • G : Matrix J J Ω)) = dotDual S (Submodule.span S (Set.range L))) :
    G.det ≠ 0 ∧ Submodule.span S (Set.range (t • G⁻¹ᵀ : Matrix J J Ω)) = Submodule.span S (Set.range L) := by
  have h1 : L * (L⁻¹ᵀ)ᵀ = 1 := by rw [transpose_transpose, mul_nonsing_inv _ (Ne.isUnit hL)]
  have h2 : L⁻¹ᵀ * Lᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ (Ne.isUnit hL), transpose_one]
  rw [dotDual_span_rows S h1] at h
  have hG : G.det ≠ 0 := by
    have h3 : ∀ i, ∃ c : J → Ω, c ᵥ* (t⁻¹ • G) = L⁻¹ᵀ i := fun i => by
      obtain ⟨c, -, hc⟩ := (mem_span_rows S _ (L⁻¹ᵀ i)).1 (h.ge (Submodule.subset_span ⟨i, rfl⟩))
      exact ⟨c, hc⟩
    choose c hc using h3
    have h4 : Matrix.of c * (t⁻¹ • G) = L⁻¹ᵀ := by
      ext i j
      exact congrFun (hc i) j
    intro h0
    have h5 := congrArg det h2
    rw [← h4, det_mul, det_mul, det_smul, h0] at h5
    simp at h5
  refine ⟨hG, ?_⟩
  rw [← dotDual_span_rows S (smul_mul_smul_inv hG ht), h, dotDual_span_rows S h2]

theorem exists_inv {G : Matrix J J Ω} (hG : ∀ i j, G i j ∈ S) (h0 : G.det ≠ 0) (h1 : G.det⁻¹ ∈ S) :
    ∃ C : Matrix J J S, (Matrix.of fun i j => (⟨G i j, hG i j⟩ : S)) * C = 1 ∧ G⁻¹ = C.map S.val := by
  set G₀ : Matrix J J S := Matrix.of fun i j => (⟨G i j, hG i j⟩ : S)
  have e : G = S.val.toRingHom.mapMatrix G₀ := rfl
  have hd : (G₀.det : Ω) = G.det := by rw [e, ← RingHom.map_det]; rfl
  have hu : IsUnit G₀.det := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
    show (G₀.det : Ω) * G.det⁻¹ = 1
    rw [hd, mul_inv_cancel₀ h0]))
  refine ⟨G₀⁻¹, mul_nonsing_inv _ hu, Matrix.inv_eq_right_inv ?_⟩
  have := congrArg S.val.toRingHom.mapMatrix (mul_nonsing_inv _ hu)
  rw [map_mul, map_one] at this
  exact this

theorem det_mem {G : Matrix J J Ω} (hG : ∀ i j, G i j ∈ S) : G.det ∈ S := by
  rw [det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hG _ _)

theorem span_eq_std {A B : Matrix J J Ω} (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (h : B * A = 1) :
    Submodule.span S (Set.range A) = Submodule.span S (Set.range fun i => Pi.single i (1 : Ω)) := by
  have e : (fun i : J => (Pi.single i (1 : Ω) : J → Ω)) = (1 : Matrix J J Ω) := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [e]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact (mem_span_rows S _ _).2 ⟨A i, hA i, vecMul_one _⟩
  · rintro _ ⟨i, rfl⟩
    exact (mem_span_rows S _ _).2 ⟨B i, hB i, by rw [← h]; rfl⟩

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] {J : Type} [Fintype J] [DecidableEq J]

def OA (p : ℕ) [Fact p.Prime] : Subalgebra ℤ (PadicAlgCl p) := subalgebraOfSubring (OO p).toSubring

theorem mem_OA (x : PadicAlgCl p) : x ∈ OA p ↔ ‖x‖ ≤ 1 := mem_OO_iff x

omit [DecidableEq J] in

theorem mem_span_OO (B : Matrix J J (PadicAlgCl p)) (v : J → PadicAlgCl p) :
    v ∈ Submodule.span (OO p) (Set.range B) ↔ ∃ c : J → PadicAlgCl p, (∀ i, ‖c i‖ ≤ 1) ∧ c ᵥ* B = v := by
  refine (Submodule.mem_span_range_iff_exists_fun (OO p) (v := (B : J → J → PadicAlgCl p))).trans ?_
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (mem_OO_iff _).1 (c i).2, by rw [vecMul_eq_sum]; rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, (mem_OO_iff _).2 (hc i)⟩, by rw [vecMul_eq_sum]; rfl⟩

omit [DecidableEq J] in

theorem mem_span_OA (B : Matrix J J (PadicAlgCl p)) (v : J → PadicAlgCl p) :
    v ∈ Submodule.span (OA p) (Set.range B) ↔ v ∈ Submodule.span (OO p) (Set.range B) := by
  simp only [mem_span_OO, mem_span_rows, mem_OA]

theorem dual_dual_OO {G L : Matrix J J (PadicAlgCl p)} {t : PadicAlgCl p} (ht : t ≠ 0) (hL : L.det ≠ 0)
    (h : ∀ w, w ∈ Submodule.span (OO p) (Set.range G) ↔
      ∀ v ∈ Submodule.span (OO p) (Set.range L), ‖w ⬝ᵥ v‖ ≤ ‖t‖) :
    G.det ≠ 0 ∧ Submodule.span (OO p) (Set.range (t • G⁻¹ᵀ : Matrix J J (PadicAlgCl p))) =
      Submodule.span (OO p) (Set.range L) := by
  have ht' : 0 < ‖t‖ := norm_pos_iff.2 ht
  obtain ⟨h1, h2⟩ := dual_dual (OA p) (G := G) ht hL (by
    ext w
    have e1 : w ∈ Submodule.span (OA p) (Set.range (t⁻¹ • G : Matrix J J _)) ↔
        t • w ∈ Submodule.span (OO p) (Set.range G) := by
      rw [mem_span_OA, mem_span_OO, mem_span_OO]
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [vecMul_smul, inv_smul_eq_iff₀ ht]
    rw [e1, h]
    refine forall_congr' fun v => ?_
    rw [mem_span_OA, mem_OA, smul_dotProduct, smul_eq_mul, norm_mul, mul_le_iff_le_one_right ht',
      dotProduct_comm])
  refine ⟨h1, ?_⟩
  ext v
  rw [← mem_span_OA, h2, mem_span_OA]

end Padic

section Val

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {J : Type} [Fintype J] [DecidableEq J]
  {K : Type} [Field K] {y : Sp K ⟶ M.Z} {ξ : M.Z}

omit [DecidableEq J] in

theorem val_vecMul (h : ∀ w, y w ⤳ ξ) {c : J → Ω} {B : Matrix J J Ω} (hc : ∀ i, c i ∈ M.O ξ)
    (hB : ∀ i j, B i j ∈ M.O ξ) :
    (fun j => M.val y ((c ᵥ* B) j)) = (fun i => M.val y (c i)) ᵥ* B.map (M.val y) := by
  ext j
  have := map_sum (RatModel.valHomOf y ξ h) (fun i => (⟨c i, hc i⟩ : M.O ξ) * ⟨B i j, hB i j⟩) Finset.univ
  simp only [map_mul, RatModel.valHomOf_apply] at this
  simpa [vecMul, dotProduct] using this

theorem val_det (h : ∀ w, y w ⤳ ξ) {B : Matrix J J Ω} (hB : ∀ i j, B i j ∈ M.O ξ) :
    M.val y B.det = (B.map (M.val y)).det := by
  set B₀ : Matrix J J (M.O ξ) := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have e : B = (M.O ξ).val.toRingHom.mapMatrix B₀ := rfl
  have hd : (B₀.det : Ω) = B.det := by rw [e, ← RingHom.map_det]; rfl
  rw [← hd, ← RatModel.valHomOf_apply y ξ h, RingHom.map_det]
  rfl

theorem val_inv (h : Set.range y = {ξ}) {B : Matrix J J Ω} (hB : ∀ i j, B i j ∈ M.O ξ)
    (h0 : (B.map (M.val y)).det ≠ 0) :
    (∀ i j, B⁻¹ i j ∈ M.O ξ) ∧ B⁻¹.map (M.val y) = (B.map (M.val y))⁻¹ := by
  rw [← val_det (RatModel.specializes_of_range_eq h) hB] at h0
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.val_ne_zero_iff h ⟨_, det_mem _ hB⟩).1 h0)
  obtain ⟨C, hC, e⟩ := exists_inv (M.O ξ) hB hu.1 hu.2
  refine ⟨fun i j => e ▸ (C i j).2, (Matrix.inv_eq_right_inv ?_).symm⟩
  have := congrArg (RatModel.valHom y ξ h).mapMatrix hC
  rw [map_mul, map_one] at this
  rw [e]
  exact this

end Val

section Spec

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {J : Type} [Fintype J]
  {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {z ξ : M.Z}

theorem span_val_image (h : y (cPt p) = z) (hξ : Set.range (gPt p ≫ y) = {ξ}) {B : Matrix J J Ω}
    (hB : ∀ i j, B i j ∈ M.O ξ) :
    Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) ''
      (Submodule.span (M.O z) (Set.range B) : Submodule (M.O z) (J → Ω))) =
      Submodule.span (OO p) (Set.range (B.map (M.val (gPt p ≫ y)))) := by
  have hs : ξ ⤳ z := by
    obtain ⟨w, rfl⟩ : ξ ∈ Set.range (gPt p ≫ y) := hξ ▸ rfl
    exact RatModel.gPt_specializes h w
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (mem_span_rows _ _ _).1 hv
    exact (mem_span_OO _ _).2 ⟨_, fun i => RatModel.norm_val_le_one h (hc i),
      (val_vecMul (RatModel.specializes_of_range_eq hξ) (fun i => RatModel.O_le_of_specializes hs (hc i)) hB).symm⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨B i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end Spec

theorem eq_zero_of_divisible {X : Type} [AddCommGroup X] [Module.Free ℤ X] {m : ℕ} (hm : 2 ≤ m)
    (h : ∀ x : X, ∃ x', m • x' = x) (x : X) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.ext_elem fun i => ?_
  exfalso
  obtain ⟨x', hx⟩ := h (b i)
  have e := congrArg (fun v => b.repr v i) hx
  simp only [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same, nsmul_eq_mul] at e
  have := Int.eq_one_of_mul_eq_one_right (by positivity) e
  omega

section Main

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens}
  {R' : Subalgebra o Ω} {hR : S.R ≤ R'} {n a : ℕ} {GG : Fin n → S.J → R'}

theorem at_test (hR' : R' ≤ M.ringOn U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z}
    {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀) (hc : M.Cen U₀ z y) (hat : S.At M y y₀)
    (hgen : ∀ (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)),
      (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p,
        w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a)
    {k : S.J → Fin n}
    (hk : M.Div (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k z)
    {t : PadicAlgCl p} (ht : ‖t‖ = τ.δ ^ a) {L : Matrix S.J S.J (PadicAlgCl p)} (hL : L.det ≠ 0)
    (hE : τ.E = Submodule.span (OO p) (Set.range L)) :
    ((Matrix.of fun i j => (GG (k i) j : Ω)).map (M.val (gPt p ≫ y))).det ≠ 0 ∧
      Submodule.span (OO p) (Set.range (t • ((Matrix.of fun i j => (GG (k i) j : Ω)).map (M.val (gPt p ≫ y)))⁻¹ᵀ :
        Matrix S.J S.J (PadicAlgCl p))) = τ.E := by
  have hξ := RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint _)
  set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _)
  have hξU : ξ ∈ U₀ := hc.2 ⟨_, rfl⟩
  have hle : R' ≤ M.O ξ := hR'.trans (RatModel.ringOn_le_O hξU)
  let y' : R' →+* PadicAlgCl p := (RatModel.valHom _ ξ hξ).comp (Subalgebra.inclusion hle).toRingHom
  obtain rfl : y₀ = y'.comp (Subalgebra.inclusion hR).toRingHom := RingHom.ext fun x => hat x
  have h1 := hgen y' τ fun b => RatModel.norm_val_le_one hc.1 ((M.O z).algebraMap_mem b)
  have h2 : Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) =
      Submodule.span (OO p) (Set.range ((Matrix.of fun i j => (GG (k i) j : Ω)).map (M.val (gPt p ≫ y)))) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨m, rfl⟩
      rw [← span_val_image (B := Matrix.of fun i j => (GG (k i) j : Ω)) hc.1 hξ fun i j => hle (GG (k i) j).2]
      refine Submodule.subset_span ⟨fun j => (GG m j : Ω), ?_, rfl⟩
      have e := span_eq_span_minor (M.O z) (fun m j => (GG m j : Ω)) k hk.1 hk.2 one_ne_zero one_ne_zero
        (by simp) (by simp)
      simp only [div_one, inv_one, one_smul] at e
      exact e.le (Submodule.subset_span ⟨m, rfl⟩)
    · rintro _ ⟨i, rfl⟩
      exact ⟨k i, rfl⟩
  have ht0 : t ≠ 0 := norm_pos_iff.1 (ht ▸ pow_pos τ.δ_pos a)
  rw [h2, hE, ← ht] at h1
  rw [hE]
  exact dual_dual_OO ht0 hL h1

theorem exists_basis [ArithBase o Ω] {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) :
    ∃ L : Matrix S.J S.J (PadicAlgCl p), L.det ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range L) ∧
      (τ.yy.ker = ⊤ → ∀ i j, ‖L i j‖ ≤ 1) := by
  obtain ⟨B, l, α, hB, hdet, -, hl, -, -, hE⟩ := GlobalTheory.ZH.exists_adapted_basis_testLattice o Ω S p y₀ τ h
  refine ⟨Matrix.of fun i j => l i * B i j, ?_, hE, fun hker i j => ?_⟩
  · rw [det_mul_column]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => norm_pos_iff.1 (hl i ▸ Real.exp_pos _)) ?_
    exact norm_pos_iff.1 (hdet ▸ one_pos)
  · have h0 : α i = 0 := by
      refine eq_zero_of_divisible (m := S.r * S.N) (by nlinarith [S.N_ge, S.r_pos]) (fun x => ?_) _
      obtain ⟨g, hg⟩ := τ.yy_onto (QuotientAddGroup.mk x)
      have : g ∈ τ.yy.ker := hker ▸ AddSubgroup.mem_top g
      rw [AddMonoidHom.mem_ker, hg, QuotientAddGroup.eq_zero_iff] at this
      exact this
    have h1 : ‖l i‖ = 1 := by rw [hl, h0]; simp
    rw [Matrix.of_apply, norm_mul, h1, _root_.one_mul]
    exact hB i j

end Main

end GlobalTheory.ZH.MinorBundle

namespace GlobalTheory.ZH
open MinorBundle

theorem exists_isEE_of_hasDiv_minors : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (R' : Subalgebra o Ω) (hR : S.R ≤ R') (n a : ℕ) (GG : Fin n → S.J → R'), S.Over₀ M U₀ → R' ≤ M.ringOn U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) → M.HasDiv (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => (GG k j : Ω) / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z := by
  intro o Ω _ _ _ _ S M U₀ R' hR n a GG hO hR' hLL hT hS hgen hd
  haveI : NeZero (S.r * S.N) := ⟨by nlinarith [S.N_ge, S.r_pos]⟩
  choose x₀ hx₀ using hO.div
  choose k hk using id hd
  have hpow : ∀ {z : M.Z} {x x' : S.Gam}, M.Div S.th x z → S.th x' ^ a / S.th x ^ a ∈ M.O z := fun h => by
    rw [← div_pow]
    exact pow_mem (h.2 _) a
  obtain ⟨EE, hEE⟩ := exists_lat_dual o Ω M S.J n (fun m j => (GG m j : Ω)) (fun z => S.th (x₀ z) ^ a)
    (fun z => ⟨pow_ne_zero _ (hx₀ z).1, ⟨_, M.isOpen_setOf_div S.th (x₀ z)⟩, hx₀ z,
      fun x hx => ⟨hpow (hx₀ x), hpow hx⟩⟩) hd
  have hmin : ∀ (z : M.Z) (x : S.Gam) (l : S.J → Fin n), M.Div S.th x z →
      M.Div (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) l z →
      Submodule.span (M.O z) (Set.range fun m j => (GG m j : Ω) / S.th x ^ a) =
        Submodule.span (M.O z) (Set.range ((S.th (x₀ z) ^ a)⁻¹ • Matrix.of fun i j => (GG (l i) j : Ω) :
          Matrix S.J S.J Ω)) := fun z x l hx hl =>
    span_eq_span_minor (M.O z) (fun m j => (GG m j : Ω)) l hl.1 hl.2 (pow_ne_zero _ hx.1)
      (pow_ne_zero _ (hx₀ z).1) (hpow (hx₀ z)) (hpow hx)
  have hE : ∀ (z : M.Z) (l : S.J → Fin n),
      M.Div (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) l z →
      EE.E z = Submodule.span (M.O z) (Set.range
        (S.th (x₀ z) ^ a • (Matrix.of fun i j => (GG (l i) j : Ω))⁻¹ᵀ : Matrix S.J S.J Ω)) := by
    intro z l hl
    obtain ⟨U, b, hz, hb, hU⟩ := EE.loc z
    rw [hU z hz]
    refine (dual_dual (M.O z) (pow_ne_zero _ (hx₀ z).1) hb ?_).2.symm
    rw [← hmin z _ l (hx₀ z) hl, ← hU z hz]
    ext w
    rw [hEE]
    exact forall₂_congr fun v _ => by rw [dotProduct_comm]
  have hval : ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∀ x,
      M.val (gPt p ≫ y) (S.th x ^ a) = M.val (gPt p ≫ y) (S.th x) ^ a := fun z p _ y hc x =>
    map_pow (RatModel.valHom _ _ (RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint _)))
      ⟨S.th x, RatModel.ringOn_le_O (hc.2 ⟨_, rfl⟩) (hO.le (S.th_mem x))⟩ a
  have hint : ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p),
      M.Cen U₀ z y → S.At M y y₀ → ∀ b : o, ‖y₀ (algebraMap o S.R b)‖ ≤ 1 := fun z p _ y y₀ hc hat b => by
    rw [hat]
    exact RatModel.norm_val_le_one hc.1 ((M.O z).algebraMap_mem b)
  have hclosed : ∀ z ∈ U₀, IsClosed ({z} : Set M.Z) →
      (Matrix.det (Matrix.of fun i j => (GG (k z i) j : Ω)))⁻¹ ∈ M.O z := by
    intro z hz hcl
    obtain ⟨p, _, y, hc⟩ := (hLL.1 U₀ le_rfl hO.ne z hcl).1
    obtain ⟨y₀, hat, hy₀, ⟨τ⟩⟩ := hT z p y hc
    obtain ⟨hsup, hH⟩ := hS z p y y₀ τ hc hat
    obtain ⟨L, hL, hEL, hL1⟩ := exists_basis τ hy₀
    have hth : ∀ x, S.th x ∈ M.O z := fun x => RatModel.ringOn_le_O hz (hO.le (S.th_mem x))
    have hthi : ∀ x, S.th x ≠ 0 → (S.th x)⁻¹ ∈ M.O z := fun x hx => RatModel.ringOn_le_O hz (hO.th_unit x hx)
    have hker : τ.yy.ker = ⊤ := by
      rw [← hH, eq_top_iff, ← S.supp]
      exact AddSubgroup.closure_mono fun x hx => ⟨hx, fun x' => by
        rw [div_eq_mul_inv]
        exact mul_mem (hth x') (hthi x hx)⟩
    have hδ : τ.δ = 1 := ((hsup _).1 (hx₀ z)).symm.trans
      ((RatModel.norm_val_eq_one_iff hc.1 (hth _)).2 ((RatModel.isUnit_O_iff _).2 ⟨(hx₀ z).1, hthi _ (hx₀ z).1⟩))
    obtain ⟨h0, hsp⟩ := at_test hR' τ hc hat (hgen p) (hk z) (t := 1) (by simp [hδ]) hL hEL
    have hG : ∀ i j, (Matrix.of fun i j => (GG (k z i) j : Ω)) i j ∈ M.O z :=
      fun i j => RatModel.ringOn_le_O hz (hR' (GG _ _).2)
    set G := Matrix.of fun i j => (GG (k z i) j : Ω)
    have hinv : ∀ i j, (G.map (M.val (gPt p ≫ y)))⁻¹ᵀ i j ∈ OA p := by
      intro i j
      have := hsp.le (Submodule.subset_span ⟨i, rfl⟩)
      rw [hEL, mem_span_OO, one_smul] at this
      obtain ⟨c, hc1, hc2⟩ := this
      rw [← hc2]
      exact sum_mem fun m _ => mul_mem ((mem_OA _).2 (hc1 m)) ((mem_OA _).2 (hL1 hker m j))
    have h1 := (mem_OA _).1 (det_mem _ hinv)
    rw [det_transpose, det_nonsing_inv, Ring.inverse_eq_inv', norm_inv,
      ← val_det (RatModel.gPt_specializes hc.1) hG] at h1
    rw [← val_det (RatModel.gPt_specializes hc.1) hG] at h0
    have h2 := RatModel.norm_val_le_one hc.1 (det_mem _ hG)
    have h3 := (inv_le_one₀ (norm_pos_iff.2 h0)).1 h1
    exact ((RatModel.isUnit_O_iff _).1
      ((RatModel.norm_val_eq_one_iff hc.1 (det_mem _ hG)).1 (le_antisymm h2 h3))).2
  refine ⟨EE, ⟨fun z hz => ?_, fun z p _ y y₀ τ hc hat => ?_⟩, fun z x hx w => ?_⟩
  · haveI := hLL.2
    obtain ⟨z', ⟨hz'U, hz'⟩, hcl⟩ := nonempty_inter_closedPoints (Z := (U₀ : Set M.Z) ∩ closure {z})
      ⟨z, hz, subset_closure rfl⟩ (U₀.isOpen.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
    have hs : z ⤳ z' := specializes_iff_mem_closure.2 hz'
    have hG : ∀ i j, (Matrix.of fun i j => (GG (k z' i) j : Ω)) i j ∈ M.O z :=
      fun i j => RatModel.ringOn_le_O hz (hR' (GG _ _).2)
    obtain ⟨C, -, hC⟩ := exists_inv (M.O z) hG (hk z').1 (RatModel.O_le_of_specializes hs (hclosed z' hz'U hcl))
    rw [hE z _ ((hk z').of_specializes hs)]
    have hA := congrArg transpose (smul_mul_smul_inv (hk z').1 (pow_ne_zero a (hx₀ z).1))
    rw [transpose_mul, transpose_transpose, transpose_one] at hA
    refine span_eq_std (M.O z) (fun i j => ?_) (fun i j => ?_) (mul_eq_one_comm.1 hA)
    · rw [hC]
      exact mul_mem (pow_mem (RatModel.ringOn_le_O hz (hO.le (S.th_mem _))) a) (C j i).2
    · rw [← inv_pow]
      exact mul_mem (pow_mem (RatModel.ringOn_le_O hz (hO.th_unit _ (hx₀ z).1)) a) (hG j i)
  · obtain ⟨L, hL, hEL, -⟩ := exists_basis τ (hint z p y y₀ hc hat)
    obtain ⟨h0, hsp⟩ := at_test hR' τ hc hat (hgen p) (hk z) (t := M.val (gPt p ≫ y) (S.th (x₀ z) ^ a))
      (by rw [hval z p y hc, norm_pow, ((hS z p y y₀ τ hc hat).1 _).1 (hx₀ z)]) hL hEL
    have hξ := RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint _)
    set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _)
    have hξU : ξ ∈ U₀ := hc.2 ⟨_, rfl⟩
    have hG : ∀ i j, (Matrix.of fun i j => (GG (k z i) j : Ω)) i j ∈ M.O ξ :=
      fun i j => RatModel.ringOn_le_O hξU (hR' (GG _ _).2)
    obtain ⟨h1, h2⟩ := val_inv hξ hG h0
    have hθ : S.th (x₀ z) ^ a ∈ M.O ξ := pow_mem (RatModel.ringOn_le_O hξU (hO.le (S.th_mem _))) a
    rw [hE z _ (hk z), span_val_image (B := S.th (x₀ z) ^ a • (Matrix.of fun i j => (GG (k z i) j : Ω))⁻¹ᵀ) hc.1 hξ
      fun i j => mul_mem hθ (h1 j i), ← hsp, ← h2]
    congr 2
    ext i j
    exact RatModel.val_mul (RatModel.specializes_of_range_eq hξ) hθ (h1 j i)
  · rw [hmin z x _ hx (hk z), ← hmin z _ _ (hx₀ z) (hk z)]
    exact hEE z w

end GlobalTheory.ZH
end
