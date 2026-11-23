import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightInvariantOfFiniteCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
open scoped TensorProduct

namespace GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

open Formalism.UG

variable {A : Type} [CommRing A]

theorem cT_mul' (σ : A →+* A) {a b c : Type} [Fintype b] (M : Matrix a b A) (N : Matrix b c A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' (σ : A →+* A) {a : Type} [DecidableEq a] : cT σ (1 : Matrix a a A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

def Unimod (S : Subring A) {n : ℕ} (U : Matrix (Fin n) (Fin n) A) : Prop :=
  (∀ i j, U i j ∈ S) ∧ ∃ U' : Matrix (Fin n) (Fin n) A, (∀ i j, U' i j ∈ S) ∧ U' * U = 1

def mixGL {n : ℕ} {e : A} (he : e * e = e) (a b : GL (Fin n) A) : GL (Fin n) A where
  val := e • a.val + (1 - e) • b.val
  inv := e • (a⁻¹).val + (1 - e) • (b⁻¹).val
  val_inv := by rw [GlobalTheory.IdemSupport.mix_mul he, Units.mul_inv, Units.mul_inv, GlobalTheory.IdemSupport.mix_self]
  inv_val := by rw [GlobalTheory.IdemSupport.mix_mul he, Units.inv_mul, Units.inv_mul, GlobalTheory.IdemSupport.mix_self]

theorem map_mixGL_one {B : Type} [CommRing B] (c : A →+* B) {n : ℕ} {e : A} (he : e * e = e) (a b : GL (Fin n) A)
    (h : c e = 1) : GeneralLinearGroup.map c (mixGL he a b) = GeneralLinearGroup.map c a := by
  ext i j
  change c (e * a.val i j + (1 - e) * b.val i j) = c (a.val i j)
  simp [h]

theorem map_mixGL_zero {B : Type} [CommRing B] (c : A →+* B) {n : ℕ} {e : A} (he : e * e = e) (a b : GL (Fin n) A)
    (h : c e = 0) : GeneralLinearGroup.map c (mixGL he a b) = GeneralLinearGroup.map c b := by
  ext i j
  change c (e * a.val i j + (1 - e) * b.val i j) = c (b.val i j)
  simp [h]

theorem one_entry_mem (S : Subring A) {n : Type} [DecidableEq n] (i j : n) : (1 : Matrix n n A) i j ∈ S := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_dual (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (hJ : cT σ J = J)
    (hu : IsUnit J) (M : GL (Fin n) A) :
    ∃ M' : GL (Fin n) A, cT σ M.val * J * M'.val = 1 ∧ cT σ M'.val * J * M.val = 1 := by
  have h1 : IsUnit (cT σ M.val) := IsUnit.of_mul_eq_one (cT σ (M⁻¹).val) (by
    rw [← cT_mul', Units.inv_mul, cT_one'])
  obtain ⟨u, hu'⟩ := h1.mul hu
  have h2 : cT σ M.val * J * (u⁻¹).val = 1 := by rw [← hu', Units.mul_inv]
  refine ⟨u⁻¹, h2, ?_⟩
  have h3 := congrArg (cT σ) h2
  have h4 : cT σ (cT σ M.val) = M.val := by ext i j; exact hσ _
  rwa [cT_mul', cT_mul', cT_one', h4, hJ, ← Matrix.mul_assoc] at h3

theorem unimod_mix (S : Subring A) (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) A)
    {e : A} (he : e * e = e) (he' : σ e * σ e = σ e) (h0 : e * σ e = 0) (hS : e ∈ S) (hS' : σ e ∈ S)
    (M M' β : GL (Fin n) A)
    (h1 : cT σ M.val * J * M'.val = 1) (h2 : cT σ M'.val * J * M.val = 1) (hU : Unimod S (cT σ β.val * J * β.val)) :
    Unimod S (cT σ (mixGL he M (mixGL he' M' β)).val * J * (mixGL he M (mixGL he' M' β)).val) := by
  obtain ⟨hi, U', hi', hU⟩ := hU
  set f := 1 - e - σ e with hf
  have v1 : (mixGL he M (mixGL he' M' β)).val = e • M.val + σ e • M'.val + f • β.val := by
    change e • M.val + (1 - e) • (σ e • M'.val + (1 - σ e) • β.val) = _
    rw [smul_add, smul_smul, smul_smul, show (1 - e) * σ e = σ e by linear_combination -h0,
      show (1 - e) * (1 - σ e) = f by rw [hf]; linear_combination h0, add_assoc]
  have v2 : cT σ (e • M.val + σ e • M'.val + f • β.val) = σ e • cT σ M.val + e • cT σ M'.val + f • cT σ β.val := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hσ, hf, map_sub, map_one]
    ring
  have a1 : σ e * e = 0 := by linear_combination h0
  have a2 : e * f = 0 := by rw [hf]; linear_combination -he - h0
  have a3 : σ e * f = 0 := by rw [hf]; linear_combination -he' - h0
  have a4 : f * e = 0 := by linear_combination a2
  have a5 : f * σ e = 0 := by linear_combination a3
  have a6 : f * f = f := by rw [hf]; linear_combination he + he' + 2 * h0
  have hfS : f ∈ S := sub_mem (sub_mem (one_mem _) hS) hS'
  have v3 : cT σ (mixGL he M (mixGL he' M' β)).val * J * (mixGL he M (mixGL he' M' β)).val =
      f • (cT σ β.val * J * β.val) + (1 - f) • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [v1, v2]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he, he', h0, a1, a2, a3, a4, a5, a6,
      zero_smul, add_zero, zero_add, h1, h2, smul_add]
    rw [show 1 - f = e + σ e by rw [hf]; ring, add_smul]
    abel
  rw [v3]
  refine ⟨fun i j => add_mem (mul_mem hfS (hi i j)) (mul_mem (sub_mem (one_mem _) hfS) (one_entry_mem S i j)),
    f • U' + (1 - f) • 1, fun i j => add_mem (mul_mem hfS (hi' i j))
      (mul_mem (sub_mem (one_mem _) hfS) (one_entry_mem S i j)), ?_⟩
  rw [GlobalTheory.IdemSupport.mix_mul a6, hU, one_mul, GlobalTheory.IdemSupport.mix_self]

def idM (A : Type) [CommRing A] (m n : ℕ) : Matrix (Fin m) (Fin n) A :=
  Matrix.of fun a b => if (a : ℕ) = b then 1 else 0

theorem idM_self (n : ℕ) : idM A n n = 1 := by
  ext a b
  simp [idM, Matrix.one_apply, Fin.ext_iff]

theorem idM_mul {m n : ℕ} (h : m = n) : idM A m n * idM A n m = 1 := by
  subst h
  rw [idM_self, Matrix.one_mul]

theorem exists_pull (S : Subring A) (σ : A →+* A) {m n : ℕ} (h : m = n) (J : Matrix (Fin m) (Fin m) A)
    (J' : Matrix (Fin n) (Fin n) A) (x : Matrix (Fin m) (Fin n) A) (x' : Matrix (Fin n) (Fin m) A)
    (hx : x * x' = 1) (hJ : cT σ x * J * x = J') (β : GL (Fin m) A) (hU : Unimod S (cT σ β.val * J * β.val)) :
    ∃ γ : GL (Fin n) A, Unimod S (cT σ γ.val * J' * γ.val) ∧ x * γ.val = β.val * idM A m n := by
  subst h
  let u : GL (Fin m) A := ⟨x', x, mul_eq_one_comm.1 hx, hx⟩
  have h1 : x * (u * β).val = β.val := by
    change x * (x' * β.val) = _
    rw [← Matrix.mul_assoc, hx, Matrix.one_mul]
  refine ⟨u * β, ?_, by rw [h1, idM_self, Matrix.mul_one]⟩
  rw [← hJ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul', Matrix.mul_assoc, h1]
  exact hU

theorem exists_push {m n : ℕ} (h : m = n) (x : Matrix (Fin m) (Fin n) A) (x' : Matrix (Fin n) (Fin m) A)
    (hx : x * x' = 1) (β : GL (Fin n) A) :
    ∃ γ : GL (Fin m) A, ∀ (a : Fin m) (b : Fin n), (a : ℕ) = b → ∀ i, γ.val i a = (x * β.val) i b := by
  subst h
  refine ⟨⟨x, x', hx, mul_eq_one_comm.1 hx⟩ * β, fun a b hab i => ?_⟩
  rw [Fin.ext hab]
  rfl

theorem int_of_spans (S : Subring A) {n : ℕ} {δ : A} (hδ : δ ∈ S) (β M : GL (Fin n) A)
    (h : ∀ x : Fin n → A, (∀ i, δ * ((β⁻¹).val *ᵥ x) i ∈ S) ↔
      ∃ c : Fin n → A, (∀ a, c a ∈ S) ∧ ∀ i, δ * x i = δ * (M.val *ᵥ c) i) :
    (∀ i j, δ * (β⁻¹ * M).val i j ∈ S) ∧ ∀ i j, δ * (M⁻¹ * β).val i j ∈ S := by
  have hs : ∀ j a : Fin n, (Pi.single j 1 : Fin n → A) a ∈ S := fun j a => by
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  constructor
  · intro i j
    have h1 := (h (M.val *ᵥ Pi.single j 1)).2 ⟨Pi.single j 1, hs j, fun _ => rfl⟩ i
    rwa [mulVec_mulVec, mulVec_single_one] at h1
  · intro i j
    obtain ⟨c, hc, h1⟩ := (h (β.val *ᵥ Pi.single j 1)).1 fun a => mul_mem hδ (by
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      exact hs j a)
    have h2 : δ • (β.val *ᵥ Pi.single j 1) = δ • (M.val *ᵥ c) := funext h1
    have h3 := congrArg (fun v => ((M⁻¹).val *ᵥ v) i) h2
    simp only [mulVec_smul, mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.smul_apply, smul_eq_mul,
      mulVec_single_one] at h3
    exact (show δ * (M⁻¹ * β).val i j = δ * c i from h3) ▸ mul_mem hδ (hc i)

end Ring

section Lattice

open Formalism.UG Formalism.UG.P GlobalTheory.NormSum.AdLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem isFrame_lat (β : GL (Fin n) 𝒜) : IsFrame β (lat β) := lat_span β

theorem eq_lat {β : GL (Fin n) 𝒜} {Λ : Submodule (𝓞 E) (Fin n → E)} (h : IsFrame β Λ)
    (hΛ : Submodule.IsLattice E Λ) : Λ = lat β := by
  ext x
  rw [mem_lat, ← h]
  conv_lhs => rw [← global_lattice_one_holds F E (Fin n) Λ (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top]
  change ((1⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) *ᵥ (fun i => ι (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ _
  rw [inv_one, Units.val_one, one_mulVec]

theorem lat_selfDual_of_unimod (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) 𝒜)
    (hg : Unimod 𝒮 (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) g.val * J.map ι * g.val)) (y : Fin n → E) :
    y ∈ lat g ↔ ∀ x ∈ lat g, hform (σ : E →+* E) J x y ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨hi, U', hi', hU⟩ := hg
  have hback : ∀ v : Fin n → 𝒜, g.val *ᵥ ((g⁻¹).val *ᵥ v) = v := by
    intro v; rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  constructor
  · intro hy x hx
    rw [mem_lat] at hx hy
    have h1 := csDual_hform_incl σ J x y
    rw [← hback (fun i => ι (x i)), ← hback (fun i => ι (y i)), hform_mulVec] at h1
    rw [← incl_mem_iff (F := F), ← h1]
    exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (csDual_sig_mem σ (hx i)) (hi i j)) (hy j)
  · intro hy
    rw [mem_lat]
    have key : ∀ j, ((cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) g.val * J.map ι * g.val) *ᵥ
        ((g⁻¹).val *ᵥ fun i => ι (y i))) j ∈ 𝒮 := by
      intro j
      have h1 := (lat_span g (g.val *ᵥ Pi.single j 1)).2 (by
        intro k
        rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _)
      have h2 := csDual_span σ J (lat g) y hy _ h1
      rwa [← hback (fun i => ι (y i)), hform_mulVec, sf_single] at h2
    intro j
    have := mulVec_int hi' key j
    rwa [mulVec_mulVec, hU, one_mulVec] at this

theorem span_eq_lat (b : Module.Basis (Fin n) E (Fin n → E)) :
    ∃ g : GL (Fin n) 𝒜, g.val = (Matrix.of fun i a => b a i).map ι ∧
      Submodule.span (𝓞 E) (Set.range b) = lat g := by
  let B : Matrix (Fin n) (Fin n) E := Matrix.of fun i a => b a i
  have hB : ∀ c, B *ᵥ c = ∑ a, c a • b a := fun c => by
    funext i
    simp [B, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hu : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.1 fun x => ⟨b.repr x, by rw [hB, b.sum_repr]⟩
  obtain ⟨g, hg⟩ := hu.map (RingHom.mapMatrix ι)
  refine ⟨g, hg, ?_⟩
  ext x
  have := mem_lat_rat g 1 B hg (b.repr x)
  rw [mul_one, hB, b.sum_repr, mem_lat_one] at this
  rw [← this, b.mem_span_iff_repr_mem (𝓞 E)]
  rfl

theorem hatL_of_hat (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ y, y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔ K *ᵥ y ∈ GlobalTheory.AdLat.hat F (Λ' : Set (Fin n → E)))
    (x : Fin n → 𝒜) : x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔
      K.map (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  let s := Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E
  have sw : ∀ (Λ : Submodule (𝓞 E) (Fin n → E)) y,
      y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔ (fun i => s (y i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    intro Λ y
    refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ y, fun h => ?_⟩
    simpa only [s, AlgEquiv.symm_apply_apply] using GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h
  have h3 := h fun i => s.symm (x i)
  rw [sw, sw] at h3
  simp only [AlgEquiv.apply_symm_apply] at h3
  refine h3.trans (iff_of_eq ?_)
  congr 1
  funext i
  simp only [mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply]
  rfl

end Lattice

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.IdemSupport Formalism.IndefR.Datum Formalism.L2.NTheta

variable {D : D7}

abbrev sg (D : D7) : Ef D →+* Ef D := Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)

abbrev OA (D : D7) : Subring (Ef D) := Formalism.L2.Herm.intAf D.host.F D.host.E

def toAd (D : D7) : Ef D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (GlobalTheory.AdeleBaseChange.exists_toAd D.host.F D.host.E).choose

theorem toAd_spec (D : D7) (x : D.host.E) (a : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :
    toAd D (x ⊗ₜ[D.host.F] a) = algebraMap _ _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a :=
  (GlobalTheory.AdeleBaseChange.exists_toAd D.host.F D.host.E).choose_spec x a

def cpt (Q : Pl D.host.E) : Ef D →+* Q.adicCompletion D.host.E :=
  (Formalism.UG.evalV D.host.E Q).toRingHom.comp (toAd D)

theorem cpt_ext {x y : Ef D} (h : ∀ Q : Pl D.host.E, cpt Q x = cpt Q y) : x = y :=
  GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D) (FiniteAdeleRing.ext _ h)

theorem mem_OA_iff (x : Ef D) : x ∈ OA D ↔ ∀ Q : Pl D.host.E, cpt Q x ∈ Q.adicCompletionIntegers D.host.E :=
  ⟨fun h => GlobalTheory.AdeleBaseChange.map_mem_int (toAd_spec D) h, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map (toAd_spec D) h⟩

theorem comp_toAd (D : D7) : Comp D ((toAd D).comp (toEAf D)) := by
  have hι := toAd_spec D
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  have hb : Function.Bijective (Formalism.IndefR.Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective
  refine ⟨fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => ?_, fun a Q => ?_⟩
  · have h3 : finPart D z = 0 := hb.1 (GlobalTheory.AdeleBaseChange.map_injective hι (by
      rw [map_zero, map_zero]; exact h2))
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he1 z).trans h1) ((he2 z).trans h3)
  · obtain ⟨y, rfl⟩ := GlobalTheory.AdeleBaseChange.map_surjective hι s
    obtain ⟨y, rfl⟩ := hb.2 y
    obtain ⟨z, hz⟩ := e.surjective (0, y)
    refine ⟨z, by rw [← he1, hz], ?_⟩
    change toAd D (Formalism.IndefR.Lev.swapAE D (finPart D z)) = _
    rw [← he2, hz]
  · exact GlobalTheory.AdeleBaseChange.map_tmul_one hι x
  · rw [mem_intAE_iff]
    exact ⟨fun h => GlobalTheory.AdeleBaseChange.map_mem_int hι h, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι h⟩
  · change toAd D ((1 : D.host.E) ⊗ₜ[D.host.F] a.2) Q = _
    rw [hι, map_one, one_mul]
    rfl

theorem exists_idem (S : Set (Pl D.host.E)) :
    ∃ e : Ef D, e * e = e ∧ e ∈ OA D ∧ (∀ Q ∈ S, cpt Q e = 1) ∧ ∀ Q ∉ S, cpt Q e = 0 := by
  classical
  obtain ⟨e, he⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨fun Q => if Q ∈ S then 1 else 0, Filter.Eventually.of_forall fun Q => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have h : ∀ Q : Pl D.host.E, cpt Q e = if Q ∈ S then 1 else 0 := fun Q => by
    change toAd D e Q = _
    rw [he]
    rfl
  refine ⟨e, cpt_ext fun Q => ?_, (mem_OA_iff e).2 fun Q => ?_, fun Q hQ => by rw [h, if_pos hQ],
    fun Q hQ => by rw [h, if_neg hQ]⟩
  · rw [map_mul, h]
    split_ifs <;> simp
  · rw [h]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem toEAf_cA (z : AE D) : toEAf D (cA D z) = sg D (toEAf D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

theorem sg_sg (z : Ef D) : sg D (sg D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x a =>
    change star (star x) ⊗ₜ[D.host.F] a = _
    rw [star_star]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem cP_cP (Q : Pl D.host.E) : cP (cP Q) = Q := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [mem_cP, mem_cP, cO_cO]

theorem natCast_mem_cP (Q : Pl D.host.E) (N : ℕ) : (N : 𝓞 D.host.E) ∈ (cP Q).asIdeal ↔ (N : 𝓞 D.host.E) ∈ Q.asIdeal := by
  rw [mem_cP, map_natCast]

theorem cpt_sg_eq_zero {Q : Pl D.host.E} {z : Ef D} (h : cpt (cP Q) z = 0) : cpt Q (sg D z) = 0 := by
  obtain ⟨δ, hδ⟩ := exists_delta (comp_toAd D) (cP Q)
  have h1 : toEAf D δ * z = 0 := cpt_ext fun P => by
    rw [map_mul, map_zero]
    by_cases hP : P = cP Q
    · rw [hP, h, mul_zero]
    · rw [show cpt P (toEAf D δ) = 0 from hδ.2.2 P hP, zero_mul]
  have h2 := delta_conj (comp_toAd D) hδ
  rw [cP_cP] at h2
  have h3 : cpt Q (sg D (toEAf D δ)) = 1 := by rw [← toEAf_cA]; exact h2.2.1
  have h4 := congrArg (fun t => cpt Q (sg D t)) h1
  simpa only [map_mul, map_zero, h3, one_mul] using h4

theorem cpt_of_isIdemAt {e : AE D} {P : Pl D.host.E} (h : IsIdemAt e P) :
    cpt P (toEAf D e) = 1 ∧ ∀ Q, Q ≠ P → cpt Q (toEAf D e) = 0 :=
  (delta_of_isIdemAt (comp_toAd D) h).2

theorem exists_isIdemAt {P : Pl D.host.E} (h : cP P ≠ P) : ∃ e : AE D, IsIdemAt e P := by
  obtain ⟨e, f, h1⟩ := exists_isPrimeIdem (comp_toAd D) P
  obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem (comp_toAd D) h1
  rcases h1 with ⟨h1, -⟩ | ⟨rfl, -⟩
  · exact ⟨e, h1⟩
  · exfalso
    have h2 := (place_comp (comp_toAd D) hε).2.1 (cP P) (under_cP P)
    rw [← hf, hd.2.2 _ h] at h2
    exact zero_ne_one h2

theorem agreeAt_of {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {a b : ℕ} {M M' : Matrix (Fin a) (Fin b) (Ef D)}
    (h : ∀ i j, cpt P (M i j) = cpt P (M' i j)) : AgreeAt P M M' := by
  refine ⟨e, he, fun i j => cpt_ext fun Q => ?_⟩
  rw [map_mul, map_mul]
  by_cases hQ : Q = P
  · rw [hQ, h]
  · rw [(cpt_of_isIdemAt he).2 Q hQ, zero_mul, zero_mul]

theorem exists_pow_mul_mem {N : ℕ} (z : Ef D)
    (h : ∀ Q : Pl D.host.E, (N : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q z ∈ Q.adicCompletionIntegers D.host.E) :
    ∃ k : ℕ, ∀ l, k ≤ l → ((N ^ l : ℕ) : Ef D) * z ∈ OA D := by
  have hfin : {Q : Pl D.host.E | cpt Q z ∉ Q.adicCompletionIntegers D.host.E}.Finite :=
    Filter.eventually_cofinite.1 (toAd D z).2
  have h1 : ∀ Q : Pl D.host.E, ∃ k : ℕ, cpt Q z ∉ Q.adicCompletionIntegers D.host.E →
      (N : Q.adicCompletion D.host.E) ^ k * cpt Q z ∈ Q.adicCompletionIntegers D.host.E := by
    intro Q
    by_cases hQ : cpt Q z ∈ Q.adicCompletionIntegers D.host.E
    · exact ⟨0, fun h => absurd hQ h⟩
    have hN : (N : 𝓞 D.host.E) ∈ Q.asIdeal := by_contra fun hN => hQ (h Q hN)
    have hv : Valued.v (N : Q.adicCompletion D.host.E) < 1 := by
      have := (Q.valuation_lt_one_iff_mem (K := D.host.E) (N : 𝓞 D.host.E)).2 hN
      rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
      simpa using this
    have h0 : Valued.v (cpt Q z) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      intro h0
      exact hQ (h0 ▸ zero_mem _)
    obtain ⟨k, hk⟩ := exists_pow_lt₀ hv (Units.mk0 _ h0)⁻¹
    refine ⟨k, fun _ => ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_pow]
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, ← one_mul (_⁻¹), lt_mul_inv_iff₀ (zero_lt_iff.2 h0)] at hk
    exact hk.le
  choose k hk using h1
  obtain ⟨K, hK⟩ := (hfin.image k).bddAbove
  refine ⟨K, fun l hl => (mem_OA_iff _).2 fun Q => ?_⟩
  rw [map_mul, map_natCast]
  by_cases hQ : cpt Q z ∈ Q.adicCompletionIntegers D.host.E
  · exact mul_mem (natCast_mem _ _) hQ
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ((hK ⟨Q, hQ, rfl⟩).trans hl)
    rw [pow_add, mul_comm (N ^ k Q), Nat.cast_mul, mul_assoc, Nat.cast_pow N (k Q)]
    exact mul_mem (natCast_mem _ _) (hk Q hQ)

abbrev loc (Q : Pl D.host.E) {n : ℕ} : GL (Fin n) (Ef D) →* GL (Fin n) (Q.adicCompletion D.host.E) :=
  GeneralLinearGroup.map (cpt Q)

def LeAt (Q : Pl D.host.E) {n : ℕ} (b a : GL (Fin n) (Ef D)) : Prop :=
  ∀ i j, cpt Q ((a⁻¹ * b).val i j) ∈ Q.adicCompletionIntegers D.host.E

theorem LeAt.congr {Q : Pl D.host.E} {n : ℕ} {b a b' a' : GL (Fin n) (Ef D)} (h : LeAt Q b a)
    (hb : loc Q b' = loc Q b) (ha : loc Q a' = loc Q a) : LeAt Q b' a' := by
  intro i j
  have : loc Q (a'⁻¹ * b') = loc Q (a⁻¹ * b) := by rw [map_mul, map_mul, map_inv, map_inv, ha, hb]
  have h2 : cpt Q ((a'⁻¹ * b').val i j) = cpt Q ((a⁻¹ * b).val i j) := congrArg (fun g => g.val i j) this
  rw [h2]
  exact h i j

theorem leAt_of_eq {Q : Pl D.host.E} {n : ℕ} {b a : GL (Fin n) (Ef D)} (h : loc Q b = loc Q a) : LeAt Q b a := by
  refine LeAt.congr (b := a) (a := a) (fun i j => ?_) h rfl
  rw [inv_mul_cancel, Units.val_one]
  exact (mem_OA_iff _).1 (one_entry_mem (OA D) i j) Q

theorem lat_le_of_leAt {n : ℕ} {b a : GL (Fin n) (Ef D)} (h : ∀ Q, LeAt Q b a) :
    GlobalTheory.NormSum.AdLattice.lat b ≤ GlobalTheory.NormSum.AdLattice.lat a :=
  GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => (mem_OA_iff _).2 fun Q => h Q i j

theorem exists_pow_smul {n N : ℕ} {b a : GL (Fin n) (Ef D)}
    (h : ∀ Q : Pl D.host.E, (N : 𝓞 D.host.E) ∉ Q.asIdeal → LeAt Q b a) :
    ∃ k : ℕ, ∀ l, k ≤ l → ∀ x ∈ GlobalTheory.NormSum.AdLattice.lat b,
      ((N ^ l : ℕ) : D.host.E) • x ∈ GlobalTheory.NormSum.AdLattice.lat a := by
  have h1 : ∀ p : Fin n × Fin n, ∃ k : ℕ, ∀ l, k ≤ l → ((N ^ l : ℕ) : Ef D) * (a⁻¹ * b).val p.1 p.2 ∈ OA D :=
    fun p => exists_pow_mul_mem _ fun Q hQ => h Q hQ p.1 p.2
  choose k hk using h1
  obtain ⟨K, hK⟩ := (Set.finite_range k).bddAbove
  refine ⟨K, fun l hl x hx => ?_⟩
  have h2 : ∀ i j, ((N ^ l : ℕ) : Ef D) * (a⁻¹ * b).val i j ∈ OA D :=
    fun i j => hk (i, j) l ((hK (Set.mem_range_self (i, j))).trans hl)
  exact GlobalTheory.NormSum.AdLattice.smul_mem_lat (g := b) (g' := a) (N ^ l) h2 hx

end Local

section Frames

open GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices GlobalTheory.IdemSupport Formalism.IndefR.Datum Formalism.L2.NTheta GlobalTheory.NormSum.AdLattice Formalism.L2.Herm

variable {D : D7}

abbrev gramOf (V : HSp D) (β : GL (Fin V.rank) (Ef D)) : Matrix (Fin V.rank) (Fin V.rank) (Ef D) :=
  Formalism.UG.cT (sg D) β.val * ratM V.gram * β.val

theorem isLattice_crdLat (V : HSp D) {L : Submodule (𝓞 D.host.E) V.V} (h : Submodule.IsLattice D.host.E L) :
    Submodule.IsLattice D.host.E (crdLat V L) := by
  refine ⟨h.fg.map _, ?_⟩
  have h1 : (crdLat V L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (L : Set V.V) := rfl
  rw [h1, ← Submodule.map_span, h.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem isSD_one {V : HSp D} {β : GL (Fin V.rank) (Ef D)} (h : crdLat V V.L0 = lat β) :
    IsSDFrame V β (crdLat V V.L0) 1 := by
  refine ⟨0, h ▸ isFrame_lat β, GlobalTheory.LevelChoices.dualL_crdLat V, one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_zero, Nat.cast_one, one_smul]
    rwa [← GlobalTheory.LevelChoices.coe_crdLat] at hx
  · rw [pow_zero, Nat.cast_one, one_smul, ← GlobalTheory.LevelChoices.coe_crdLat]
    exact hx

theorem exists_base (V : HSp D) : ∃ β : GL (Fin V.rank) (Ef D), crdLat V V.L0 = lat β := by
  have hL := isLattice_crdLat V V.standardTuple_isLattice
  obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ hL.fg hL.span_eq_top
  exact ⟨β, eq_lat hβ hL⟩

theorem unimod_of_isSD {V : HSp D} {β : GL (Fin V.rank) (Ef D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (h : IsSDFrame V β Λ N) :
    Unimod (OA D) (gramOf V β) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.gram_unimodular D V β Λ _ hc
  have hG' : (intGL D.host.F D.host.E V.rank G).val = gramOf V β := hG
  rw [← hG']
  refine ⟨fun i j => (G.val i j).2, (intGL D.host.F D.host.E V.rank G⁻¹).val, fun i j => ((G⁻¹).val i j).2, ?_⟩
  rw [map_inv, Units.inv_mul]

theorem mem_lat_iff_dual {V : HSp D} {β : GL (Fin V.rank) (Ef D)} (h : Unimod (OA D) (gramOf V β))
    (y : Fin V.rank → D.host.E) : y ∈ lat β ↔ y ∈ dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (lat β) :=
  lat_selfDual_of_unimod D.sp.cm.sig V.gram β h y

theorem dualL_lat {V : HSp D} {β : GL (Fin V.rank) (Ef D)} (h : Unimod (OA D) (gramOf V β)) :
    dualL D.sp.cm V (lat β) = lat β := by
  unfold dualL
  conv_rhs => rw [← Submodule.span_eq (lat β)]
  congr 1
  ext y
  exact (mem_lat_iff_dual h y).symm

theorem cT_gram (V : HSp D) : Formalism.UG.cT (sg D) (ratM V.gram) = ratM V.gram := by
  ext i j
  change (star (V.gram j i)) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) = V.gram i j ⊗ₜ[D.host.F] 1
  rw [show star (V.gram j i) = V.gram i j from V.herm.eq _ _]

theorem isUnit_gram (V : HSp D) : IsUnit (ratM V.gram) :=
  ((Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V)).map (RingHom.mapMatrix (eToEAf D))

theorem exists_frame (V : HSp D) {N : ℕ} (hN : 0 < N) (β₀ : GL (Fin V.rank) (Ef D)) (h₀ : crdLat V V.L0 = lat β₀)
    (S S' : Set (Pl D.host.E)) (hS : ∀ Q ∈ S, (N : 𝓞 D.host.E) ∈ Q.asIdeal ∧ cP Q ∉ S)
    (M M₁ : GL (Fin V.rank) (Ef D))
    (hS' : ∀ Q ∈ S', (N : 𝓞 D.host.E) ∉ Q.asIdeal ∧ LeAt Q M₁ β₀ ∧ LeAt Q β₀ M₁) :
    ∃ β Λ, IsSDFrame V β Λ N ∧ (∀ Q ∈ S, loc Q β = loc Q M) ∧ ∀ Q ∈ S', loc Q β = loc Q M₁ := by
  obtain ⟨e, he, heO, he1, he0⟩ := exists_idem S
  obtain ⟨f, hf, -, hf1, hf0⟩ := exists_idem S'
  have he' : sg D e * sg D e = sg D e := by rw [← RingHom.map_mul, he]
  have h0 : e * sg D e = 0 := cpt_ext fun Q => by
    rw [RingHom.map_mul, RingHom.map_zero]
    by_cases hQ : Q ∈ S
    · rw [cpt_sg_eq_zero (he0 _ (hS Q hQ).2), mul_zero]
    · rw [he0 Q hQ, zero_mul]
  obtain ⟨M', h1, h2⟩ := exists_dual (sg D) sg_sg _ (cT_gram V) (isUnit_gram V) M
  have hU := unimod_mix (OA D) (sg D) sg_sg _ he he' h0 heO (Formalism.UG.P.csDual_sig_mem _ heO) M M' β₀ h1 h2
    (unimod_of_isSD (isSD_one h₀))
  have b1 : ∀ Q ∈ S, loc Q (mixGL he M (mixGL he' M' β₀)) = loc Q M := fun Q hQ => map_mixGL_one _ _ _ _ (he1 Q hQ)
  have b2 : ∀ Q : Pl D.host.E, (N : 𝓞 D.host.E) ∉ Q.asIdeal → loc Q (mixGL he M (mixGL he' M' β₀)) = loc Q β₀ :=
    fun Q hQ => (map_mixGL_zero _ _ _ _ (he0 Q fun h => hQ (hS Q h).1)).trans (map_mixGL_zero _ _ _ _
      (cpt_sg_eq_zero (he0 _ fun h => hQ ((natCast_mem_cP Q N).1 (hS _ h).1))))
  generalize mixGL he M (mixGL he' M' β₀) = β₁ at hU b1 b2
  have c1 : ∀ Q ∈ S', loc Q (mixGL hf M₁ β₁) = loc Q M₁ := fun Q hQ => map_mixGL_one _ _ _ _ (hf1 Q hQ)
  have c2 : ∀ Q ∉ S', loc Q (mixGL hf M₁ β₁) = loc Q β₁ := fun Q hQ => map_mixGL_zero _ _ _ _ (hf0 Q hQ)
  generalize mixGL hf M₁ β₁ = β at c1 c2
  have hl : lat β = lat β₁ := by
    refine le_antisymm (lat_le_of_leAt fun Q => ?_) (lat_le_of_leAt fun Q => ?_)
    · by_cases hQ : Q ∈ S'
      · exact (hS' Q hQ).2.1.congr (c1 Q hQ) (b2 Q (hS' Q hQ).1)
      · exact leAt_of_eq (c2 Q hQ)
    · by_cases hQ : Q ∈ S'
      · exact (hS' Q hQ).2.2.congr (b2 Q (hS' Q hQ).1) (c1 Q hQ)
      · exact leAt_of_eq (c2 Q hQ).symm
  obtain ⟨k, hk⟩ := exists_pow_smul (N := N) (b := β₀) (a := β₁) fun Q hQ => leAt_of_eq (b2 Q hQ).symm
  obtain ⟨k', hk'⟩ := exists_pow_smul (N := N) (b := β₁) (a := β₀) fun Q hQ => leAt_of_eq (b2 Q hQ)
  refine ⟨β, lat β₁, ⟨max k k', hl ▸ isFrame_lat β, dualL_lat hU, pow_pos hN _, fun x hx => ?_, fun x hx => ?_⟩,
    fun Q hQ => (c2 Q fun h => (hS' Q h).1 (hS Q hQ).1).trans (b1 Q hQ), c1⟩
  · rw [← GlobalTheory.LevelChoices.coe_crdLat, h₀] at hx
    exact hk _ (le_max_left _ _) x hx
  · rw [← GlobalTheory.LevelChoices.coe_crdLat, h₀]
    exact hk' _ (le_max_right _ _) x hx

theorem cpt_mem_of_mul {Q : Pl D.host.E} {δ z : Ef D} (e1 : cpt Q δ = 1) (h : δ * z ∈ OA D) :
    cpt Q z ∈ Q.adicCompletionIntegers D.host.E := by
  have := (mem_OA_iff _).1 h Q
  rwa [RingHom.map_mul, e1, one_mul] at this

set_option maxHeartbeats 800000 in
theorem leAt_of_spansAt {V : HSp D} {β₀ M : GL (Fin V.rank) (Ef D)} (h₀ : crdLat V V.L0 = lat β₀) {Q : Pl D.host.E}
    (h : SpansAt Q V M.val) : LeAt Q M β₀ ∧ LeAt Q β₀ M := by
  obtain ⟨e, he, h⟩ := h
  obtain ⟨e1, e0⟩ := cpt_of_isIdemAt he
  generalize toEAf D e = δ at h e1 e0
  have hδ : δ ∈ OA D := (mem_OA_iff _).2 fun P => by
    by_cases hP : P = Q
    · rw [hP, e1]; exact one_mem _
    · rw [e0 P hP]; exact zero_mem _
  have hfr : ∀ x : Fin V.rank → Ef D, (fun i => δ * x i) ∈ hatL (F := D.host.F) (crdLat V V.L0) ↔
      ∀ i, δ * ((β₀⁻¹).val *ᵥ x) i ∈ OA D := fun x => by
    rw [h₀, isFrame_lat β₀, show (fun i => δ * x i) = δ • x from rfl, mulVec_smul]
    rfl
  obtain ⟨h1, h2⟩ := int_of_spans (OA D) hδ β₀ M fun x => (hfr x).symm.trans (h x)
  exact ⟨fun i j => cpt_mem_of_mul e1 (h1 i j), fun i j => cpt_mem_of_mul e1 (h2 i j)⟩

theorem exists_unitary (V : HSp D) (γ : GL (Fin V.rank) (Ef D)) (hγ : Unimod (OA D) (gramOf V γ)) :
    ∃ k : GL (Fin V.rank) (Ef D), gramOf V k = ratM V.gram ∧ crdLat V V.L0 = lat (k⁻¹ * γ) := by
  let L : Submodule (𝓞 D.host.E) V.V :=
    (lat γ).comap ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E))
  have hL : crdLat V L = lat γ := Submodule.map_comap_eq_of_surjective
    (f := (crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).surjective _
  have hm : ∀ x, x ∈ L ↔ crd V x ∈ lat γ := fun _ => Iff.rfl
  have h1 : Submodule.IsLattice D.host.E L := by
    refine ⟨Submodule.fg_of_fg_map_injective
      ((crd V : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) (crd V).injective
      (hL ▸ (lat_isLattice γ).fg : (crdLat V L).FG), ?_⟩
    apply Submodule.map_injective_of_injective (f := (crd V).toLinearMap) (crd V).injective
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← (lat_isLattice γ).span_eq_top, ← hL]
    rfl
  have h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L := by
    ext x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    rw [hm, mem_lat_iff_dual hγ]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := (crd V).surjective y
      have := h y hy
      rw [hT_crd D.sp.cm] at this
      exact this
    · intro h y hy
      rw [hT_crd D.sp.cm]
      exact h _ hy
  obtain ⟨k, -, hk⟩ := GlobalTheory.VolumeRatioTypings.exists_conj V L h1 h2
  refine ⟨Formalism.IndefR.Lev.finE V k, GlobalTheory.LevSplit.finE_mem_UA V k, eq_lat (fun x => ?_) (isLattice_crdLat V V.standardTuple_isLattice)⟩
  have hk' : ∀ y, y ∈ GlobalTheory.AdLat.hat D.host.F (crdLat V V.L0 : Set (Fin V.rank → D.host.E)) ↔
      finMat D.sp.cm.sig V.gram k *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (lat γ : Set (Fin V.rank → D.host.E)) := by
    rw [← hL, GlobalTheory.LevelChoices.coe_crdLat]
    have := GlobalTheory.LevelChoices.coe_crdLat (GlobalTheory.VolRatioCompare.reLat V L h1 h2)
    rw [← this] at hk
    exact hk
  refine (hatL_of_hat _ _ _ hk' x).trans ((isFrame_lat γ _).trans ?_)
  rw [mulVec_mulVec, _root_.mul_inv_rev, inv_inv, Units.val_mul]
  rfl

end Frames

end GlobalTheory.StdFrames
