import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosureProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentConstantTermFormFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleStandardOpensIffStatement
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section Vals
variable {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {e : B →ₐ[ℂ] ℂ}

private lemma val_mul (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v * v') (c * c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨mul_mem p p', map_mul ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_add (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v + v') (c + c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨add_mem p p', map_add ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_zero (hV : ValBasic) : Val B e (0 : L) 0 := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact (hev _ _).2 ⟨zero_mem _, map_zero ev⟩

private lemma val_sum (hV : ValBasic) {ι : Type} (s : Finset ι) (f : ι → L) (c : ι → ℂ)
    (h : ∀ i ∈ s, Val B e (f i) (c i)) : Val B e (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_zero hV
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact val_add hV (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma val_unique (hV : ValBasic) {v : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v c') :
    c = c' := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  rfl

private lemma val_of_mem (hV : ValBasic) {v : L} (h : v ∈ loc B e) : ∃ c, Val B e v c := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact ⟨_, (hev _ _).2 ⟨h, rfl⟩⟩

end Vals

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma acts_expand (τ : DR ℂ K →ₗ[K] K) {m : ℕ} (w' w : Fin m → DR ℂ K) (v : DR ℂ K) :
    mulP F K (muP F K τ (∑ k, w' k ⊗ₜ w k) v) =
      ∑ k, algebraMap F K (Algebra.trace F K (τ (w' k * v))) • w k := by
  simp only [map_sum, LinearMap.sum_apply, muP_tmul, mulP_tmul]

private lemma omG_ne {d : ℕ} (x : Fin (d + 1) → Fˣ) : algebraMap F K (omG x 0) ≠ 0 := by
  refine (map_ne_zero _).2 ?_
  exact Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.idVal_of :
    LocForms → DtBasic → CRT → TrVal → ResVal → LatA → ValBasic → OmLoc → IdVal := by
  intro hLF hDt hCRT hTV hRV hLat hV hOL F K _ _ _ _ _ _ d x cov τ hτ red a ha m w' w hw hact z
  classical
  obtain ⟨hli, hdt, hvol, -, -⟩ := hDt F K d x cov τ hτ
  set B := rB ℂ K (xv x) ({0} : Finset (Fin (d + 1))) with hB
  set om : K := algebraMap F K (omG x 0) with hom
  have omne : om ≠ 0 := omG_ne x
  have hτv : τ (dtS K x Finset.univ) = om := by
    rw [hvol, map_smul, hτ.1, smul_eq_mul, mul_one]
  have hgEq : ∀ y ∈ omB ℂ K B d, y = (τ y / om) • dtS K x Finset.univ := by
    intro y hy
    have h1 := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K d (xv x) cov).2 τ hτ y (mem_deg_of_mem_omB B d y hy)
    rw [hvol, smul_smul, div_mul_cancel₀ _ omne]
    exact h1
  have hgLoc : ∀ (e : fib ℂ K (xv x)), ∀ y ∈ omB ℂ K B d, τ y / om ∈ loc B e.1 := by
    intro e y hy
    have hle : B ≤ loc B e.1 := (hV K B e.1).1
    have hy' := (hOL K B e.1 d).2.2 _ hle hy
    obtain ⟨c, hc, hce⟩ := (hLF F K d x cov red e d y).1 hy'
    have hp : Finset.univ.powersetCard d = ({Finset.univ} : Finset (Finset (Fin d))) := by
      have := Finset.powersetCard_self (Finset.univ : Finset (Fin d))
      simpa using this
    rw [hp, Finset.sum_singleton] at hce
    have : τ y = c Finset.univ * om := by
      rw [hce, map_smul, hτv, smul_eq_mul]
    rw [this, mul_div_cancel_right₀ _ omne]
    exact hc _
  have hyB : ∀ k (S : Finset (Fin d)), S.card = a → w' k * dtS K x S ∈ omB ℂ K B d := by
    intro k S hS
    have := mul_mem_omB B (d - a) a _ (hw k).1 _ (hS ▸ hdt S)
    rwa [Nat.sub_add_cancel ha] at this
  have hwL : ∀ k, ∃ c : Finset (Fin d) → K, (∀ S, c S ∈ loc B z.1) ∧
      w k = ∑ S ∈ Finset.univ.powersetCard a, c S • dtS K x S := fun k =>
    (hLF F K d x cov red z a (w k)).1 ((hOL K B z.1 a).2.2 _ (hV K B z.1).1 (hw k).2)
  choose b hbl hbe using hwL
  have hφ : ∀ v : K, ∃ c : ℂ, v ∈ loc B z.1 → Val B z.1 v c := by
    intro v
    by_cases hv : v ∈ loc B z.1
    · obtain ⟨c, hc⟩ := val_of_mem hV hv
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose φ hφ using hφ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_laurentConstantTermForm_functionField ℂ F d (xv x) cov.pd
  refine ⟨fun k S => τ (w' k * dtS K x S) / om, b, fun k S => φ (τ (w' k * dtS K x S) / om),
    fun k T => φ (b k T), fun k S hS => hgEq _ (hyB k S hS), hbe, fun k S hS =>
      ⟨hφ _ (hgLoc z _ (hyB k S hS)), hφ _ (hbl k S)⟩, ?_⟩
  intro S T hS hT
  obtain ⟨h, hh⟩ := (hCRT F K d x cov).2 (fun e => if e = z then 1 else 0)
  set g : Fin m → K := fun k => τ (w' k * dtS K x S) / om with hg
  set t : Fin m → F := fun k => Algebra.trace F K (g k * h) with ht
  have hgy : ∀ k, τ (w' k * dtS K x S) = om * g k := by
    intro k
    simp only [hg]
    field_simp
  have htr : ∀ k, Algebra.trace F K (om * (g k * h)) = omG x 0 * t k := by
    intro k
    rw [hom, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have claim1 : ∀ k, t k ∈ rA ℂ (xv x) {0} := by
    intro k
    have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K d (xv x) cov τ hτ {0} ⟨0, by simp⟩ (om * (g k * h))).2
      ⟨(h : K) • (w' k * dtS K x S), smul_mem_omB B d _ h.2 _ (hyB k S hS), by
        rw [map_smul, hgy, smul_eq_mul]; ring⟩ 1 (Subalgebra.one_mem _)
    rw [mul_one, htr] at h1
    have h2 := ((hLat F d x cov.pd {0} 0 (by simp)).2.1 _).1 h1
    have hne : omG x 0 ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero
    rwa [mul_div_cancel_left₀ _ hne] at h2
  have claim2 : ∀ k, Val B z.1 (algebraMap F K (t k)) (φ (g k)) := by
    intro k
    have hres := hRV F K d x cov ρ hρ z (t k) (claim1 k)
    have hγ0 : ∀ e : fib ℂ K (xv x), ∃ c, Val B e.1 (g k) c := fun e =>
      val_of_mem hV (hgLoc e _ (hyB k S hS))
    choose γ0 hγ0 using hγ0
    have hγ : ∀ e : fib ℂ K (xv x), Val B e.1 (g k * h) (γ0 e * e.1 h) := fun e =>
      val_mul hV (hγ0 e) ((hV K B e.1).2.2.1 h)
    have htv := hTV F K d x cov red ρ hρ (g k * h) (fun e => γ0 e * e.1 h) hγ (claim1 k)
    have hfs : ∑ᶠ e, γ0 e * e.1 h = φ (g k) := by
      rw [finsum_eq_single _ z]
      · rw [hh z]
        simp only [if_true, mul_one]
        exact val_unique hV (hγ0 z) (hφ _ (hgLoc z _ (hyB k S hS)))
      · intro e he
        rw [hh e, if_neg he, mul_zero]
    have : ρ (t k) = φ (g k) := by rw [← hfs]; exact htv
    rwa [this] at hres
  have claim3 : ∑ k, algebraMap F K (t k) • w k = (h : K) • dtS K x S := by
    have h1 := hact ((h : K) • dtS K x S)
      (Submodule.smul_mem _ _ (hS ▸ mem_deg_of_mem_omB B _ _ (hdt S)))
    rw [acts_expand] at h1
    have h2 : ∀ k, algebraMap F K (Algebra.trace F K (τ (w' k * ((h : K) • dtS K x S)))) • w k =
        om • (algebraMap F K (t k) • w k) := by
      intro k
      rw [mul_smul_comm, map_smul, hgy, smul_eq_mul,
        show (h : K) * (om * g k) = om * (g k * h) by ring, htr, map_mul, mul_smul]
    simp only [h2, ← Finset.smul_sum] at h1
    exact smul_right_injective _ omne h1
  have claim4 : ∀ T ∈ Finset.univ.powersetCard a,
      ∑ k, algebraMap F K (t k) * b k T = if S = T then (h : K) else 0 := by
    have hsum : ∑ T ∈ Finset.univ.powersetCard a,
        ((∑ k, algebraMap F K (t k) * b k T) - if S = T then (h : K) else 0) • dtS K x T = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, ← hbe]
      rw [claim3, Finset.sum_ite_eq, if_pos (by simp [Finset.mem_powersetCard, hS]), sub_self]
    intro T hT
    exact sub_eq_zero.1 (linearIndependent_iff'.1 hli _ _ hsum T hT)
  have hTm : T ∈ Finset.univ.powersetCard a := by simp [Finset.mem_powersetCard, hT]
  have hL : Val B z.1 (∑ k, algebraMap F K (t k) * b k T) (∑ k, φ (g k) * φ (b k T)) :=
    val_sum hV _ _ _ fun k _ => val_mul hV (claim2 k) (hφ _ (hbl k T))
  rw [claim4 T hTm] at hL
  have hz1 : Val B z.1 (h : K) 1 := by
    have := (hV K B z.1).2.2.1 h
    rwa [hh z, if_pos rfl] at this
  by_cases hST : S = T
  · rw [if_pos hST] at hL ⊢
    exact val_unique hV hL hz1
  · rw [if_neg hST] at hL ⊢
    exact val_unique hV hL (val_zero hV)
