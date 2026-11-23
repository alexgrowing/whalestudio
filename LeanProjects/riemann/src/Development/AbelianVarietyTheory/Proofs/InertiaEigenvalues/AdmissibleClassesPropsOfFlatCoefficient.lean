import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow

noncomputable section

namespace GlobalTheory.AdmClasses

open GlobalTheory.AdmLoc TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 H1)

section General

variable {O G : Type} [CommRing O] [Group G]

structure ClosedClass (Ad : ∀ (M : Type) [AddCommGroup M] [Module O M], Representation O G M → Prop) : Prop where
  sub : ∀ {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M'), (∀ σ x, f (π σ x) = π' σ (f x)) →
    Function.Injective f → Ad M' π' → Ad M π
  quot : ∀ {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'} (f : M →ₗ[O] M'), (∀ σ x, f (π σ x) = π' σ (f x)) →
    Function.Surjective f → Ad M π → Ad M' π'
  prod : ∀ {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'}, Ad M π → Ad M' π' → Ad (M × M') (π.prod π')

theorem closedClass_finite : ClosedClass (O := O) (G := G) (fun M _ _ _ => Finite M) where
  sub f _ hf _ := Finite.of_injective f hf
  quot f _ hf _ := Finite.of_surjective f hf
  prod _ _ := inferInstance

variable {Ad : ∀ (M : Type) [AddCommGroup M] [Module O M], Representation O G M → Prop}

theorem ClosedClass.twist (h : ClosedClass Ad) (χ : G →* Oˣ) :
    ClosedClass (fun M _ _ π => Ad M (twistRep π χ)) where
  sub f hf hi ha := h.sub f (fun σ x => by rw [twistRep_apply, twistRep_apply, map_smul, hf]) hi ha
  quot f hf hs ha := h.quot f (fun σ x => by rw [twistRep_apply, twistRep_apply, map_smul, hf]) hs ha
  prod ha hb := h.sub LinearMap.id
    (fun σ x => Prod.ext (by simp [twistRep_apply]) (by simp [twistRep_apply])) Function.injective_id (h.prod ha hb)

variable [TopologicalSpace G]
variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  {π : Representation O G M} {π' : Representation O G M'}

def lower {c c' : O} (h : c ∣ c') : (O ⧸ Ideal.span {c'}) →ₗ[O] (O ⧸ Ideal.span {c}) :=
  Submodule.factor (Ideal.span_singleton_le_span_singleton.mpr h)

theorem lower_mk {c c' : O} (h : c ∣ c') (y : O) :
    lower h (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y := rfl

theorem ClosedClass.push (h : ClosedClass Ad) {c c' : O} (hcc : c' ∣ c) (hc : ∀ m : M, c • m = 0)
    (hc' : ∀ m : M', c' • m = 0) (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (z : ↥(Z1 π ⊤)) (z' : ↥(Z1 π' ⊤)) (hz : ∀ g, (z' : G → M') g = f ((z : G → M) g))
    (h1 : Ad _ (extRep π hc z)) (h2 : Ad _ π') : Ad _ (extRep π' hc' z') := by
  refine h.quot ((LinearMap.inl O M' _).coprod (f.prodMap (lower hcc))) ?_ ?_ (h.prod h2 h1)
  · rintro σ ⟨m', m, q⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine Prod.ext ?_ ?_
    · simp [extRep_apply, lower_mk, hf, hz]
      abel
    · simp [extRep_apply, lower_mk]
  · rintro ⟨m', q⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨(m', (0, Ideal.Quotient.mk _ y)), by simp [lower_mk]⟩

theorem ClosedClass.pull (h : ClosedClass Ad) {c c' : O} (hcc : c' ∣ c) (hc : ∀ m : M, c • m = 0)
    (hc' : ∀ m : M', c' • m = 0) (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hi : Function.Injective f)
    (z : ↥(Z1 π ⊤)) (z' : ↥(Z1 π' ⊤)) (hz : ∀ g, (z' : G → M') g = f ((z : G → M) g))
    (h1 : Ad _ (extRep π' hc' z')) (h2 : Ad _ (Representation.trivial O G (O ⧸ Ideal.span {c}))) :
    Ad _ (extRep π hc z) := by
  refine h.sub ((f.prodMap (lower hcc)).prod (LinearMap.snd O M _)) ?_ ?_ (h.prod h1 h2)
  · rintro σ ⟨m, q⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [extRep_apply, lower_mk, hf, hz]
  · rintro ⟨m, q⟩ ⟨m₂, q₂⟩ he
    have e1 := congrArg (fun p => p.1.1) he
    have e2 := congrArg (fun p => p.2) he
    simp only [LinearMap.prod_apply, LinearMap.prodMap_apply, LinearMap.snd_apply, Function.prod] at e1 e2
    exact Prod.ext (hi e1) e2

def pairZ (z : ↥(Z1 π ⊤)) (z' : ↥(Z1 π' ⊤)) : ↥(Z1 (π.prod π') ⊤) :=
  ⟨fun g => ((z : G → M) g, (z' : G → M') g), ⟨z.2.1.1.prodMk z'.2.1.1, fun _ => Submodule.mem_top⟩, by
    funext x
    exact Prod.ext (congrFun z.2.2 x) (congrFun z'.2.2 x)⟩

theorem ClosedClass.add (h : ClosedClass Ad) {c : O} (hc : ∀ m : M, c • m = 0) (z z' : ↥(Z1 π ⊤))
    (h1 : Ad _ (extRep π hc z)) (h2 : Ad _ (extRep π hc z')) (h3 : Ad _ π) : Ad _ (extRep π hc (z + z')) := by
  have hc₂ : ∀ m : M × M, c • m = 0 := fun m => Prod.ext (hc m.1) (hc m.2)
  have hpz : ∀ σ, ((pairZ z z' : ↥(Z1 (π.prod π) ⊤)) : G → M × M) σ = ((z : G → M) σ, (z' : G → M) σ) :=
    fun _ => rfl
  have hp : Ad _ (extRep (π.prod π) hc₂ (pairZ z z')) := by
    refine h.sub (((LinearMap.fst O M M ∘ₗ LinearMap.fst _ _ _).prod (LinearMap.snd _ _ _)).prod
      ((LinearMap.snd O M M ∘ₗ LinearMap.fst _ _ _).prod (LinearMap.snd _ _ _))) ?_ ?_ (h.prod h1 h2)
    · rintro σ ⟨⟨m, m'⟩, q⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
      simp [extRep_apply, hpz]
    · rintro ⟨⟨m, m'⟩, q⟩ ⟨⟨m₂, m₂'⟩, q₂⟩ he
      have e1 := congrArg (fun p => p.1.1) he
      have e2 := congrArg (fun p => p.2.1) he
      have e3 := congrArg (fun p => p.1.2) he
      simp only [LinearMap.prod_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, Function.prod] at e1 e2 e3
      rw [e1, e2, e3]
  refine h.quot ((LinearMap.id.coprod LinearMap.id).prodMap LinearMap.id) ?_ ?_ hp
  · rintro σ ⟨⟨m, m'⟩, q⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine Prod.ext ?_ ?_
    · simp [extRep_apply, hpz, smul_add]
      abel
    · simp [extRep_apply, hpz]
  · rintro ⟨m, q⟩
    exact ⟨((m, 0), q), by simp⟩

theorem ClosedClass.zero (h : ClosedClass Ad) {c : O} (hc : ∀ m : M, c • m = 0) (h1 : Ad _ π)
    (h2 : Ad _ (Representation.trivial O G (O ⧸ Ideal.span {c}))) : Ad _ (extRep π hc 0) := by
  refine h.sub LinearMap.id ?_ Function.injective_id (h.prod h1 h2)
  rintro σ ⟨m, q⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [extRep_apply]
  simp

theorem ClosedClass.level (h : ClosedClass Ad) {lam : O} {a b : ℕ} (ha : ∀ m : M, lam ^ a • m = 0)
    (hb : ∀ m : M, lam ^ b • m = 0) (z : ↥(Z1 π ⊤)) (h1 : Ad _ π)
    (h2 : Ad _ (Representation.trivial O G (O ⧸ Ideal.span {lam ^ b})))
    (h3 : Ad _ (extRep π ha z)) : Ad _ (extRep π hb z) := by
  rcases le_total a b with hab | hab
  · exact h.pull (pow_dvd_pow lam hab) hb ha LinearMap.id (fun _ _ => rfl) Function.injective_id z z
      (fun _ => rfl) h3 h2
  · exact h.push (pow_dvd_pow lam hab) ha hb LinearMap.id (fun _ _ => rfl) z z (fun _ => rfl) h3 h1

end General

section Ring

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem exists_pow_smul_eq_zero [CharZero O] {lam : O} (hl : Irreducible lam) (X : Type) [AddCommGroup X]
    [Module O X] [Finite X] : ∃ a : ℕ, 1 ≤ a ∧ ∀ x : X, lam ^ a • x = 0 := by
  have hN : ((Nat.card X : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hN hl
  have hk : ∀ x : X, lam ^ k • x = 0 := fun x => by
    have e : lam ^ k = ((u⁻¹ : Oˣ) : O) * ((Nat.card X : ℕ) : O) := by
      rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, mul_smul, Nat.cast_smul_eq_nsmul, card_nsmul_eq_zero', smul_zero]
  exact ⟨k + 1, Nat.le_add_left 1 k, fun x => by rw [pow_succ', mul_smul, hk, smul_zero]⟩

theorem finite_quot_pow {lam p : O} (hl : Irreducible lam) (hp : ¬ IsUnit p) (a : ℕ)
    [Finite (O ⧸ Ideal.span {p ^ a})] : Finite (O ⧸ Ideal.span {lam ^ a}) := by
  have hdvd : lam ∣ p := by
    have hm : p ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal p).mpr hp
    rwa [(IsDiscreteValuationRing.irreducible_iff_uniformizer lam).mp hl, Ideal.mem_span_singleton] at hm
  have hs : Function.Surjective (lower (pow_dvd_pow_of_dvd hdvd a)) := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨Ideal.Quotient.mk _ y, lower_mk _ y⟩
  exact Finite.of_surjective _ hs

end Ring

section Classes

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {t : ℕ} {Ut : ZMod n → Multiset ℤ}
    {M : Type} [AddCommGroup M] [Module O M] {W : Representation O G M}

omit [TopologicalSpace G] in

theorem lTensor_twCoef (χ : G →* Oˣ) {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X'] [Module O X']
    (f : X →ₗ[O] X') (g : G) (m : M ⊗[O] X) :
    f.lTensor M (twCoef W χ X g m) = twCoef W χ X' g (f.lTensor M m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => simp only [twCoef, coefRep_tmul, LinearMap.lTensor_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem exists_coefH1_mk (χ : G →* Oˣ) {X X' : Type} [AddCommGroup X] [Module O X] [AddCommGroup X']
    [Module O X'] (f : X →ₗ[O] X') (z : ↥(Z1 (twCoef W χ X) ⊤)) :
    ∃ z' : ↥(Z1 (twCoef W χ X') ⊤), coefH1 W χ f (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ g, (z' : G → M ⊗[O] X') g = f.lTensor M ((z : G → M ⊗[O] X) g) := ⟨_, rfl, fun _ => rfl⟩

private theorem mem_admAt_of_mem_admAt (hcl : ClosedClass (fun (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N) =>
      Admissible PD emb Γ t Ut π))
    (hW : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], Admissible PD emb Γ t Ut (coefRep W X))
    (hχ : ∀ a : ℕ, Admissible PD emb Γ t Ut
      (twistRep (Representation.trivial O G (O ⧸ Ideal.span {Γ.lam ^ a})) Γ.χ₁))
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] {a b : ℕ}
    (ha : ∀ x : X, Γ.lam ^ a • x = 0) (hb : ∀ x : X, Γ.lam ^ b • x = 0) {c : H1 (twCoef W Γ.χ₁ X) ⊤}
    (hc : c ∈ admAt PD emb Γ t Ut W X a ha) : c ∈ admAt PD emb Γ t Ut W X b hb := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [mk_mem_admissibleAt_iff_cocycle] at hc ⊢
  have hπ : Admissible PD emb Γ t Ut (twistRep (twCoef W Γ.χ₁ X) Γ.χ₁) := by
    rw [twist_twCoef]
    exact hW X
  exact (hcl.twist Γ.χ₁).level (smul_tensor_eq_zero ha) (smul_tensor_eq_zero hb) z hπ (hχ b) hc

theorem admissible_classes_props_of_flat_coefficient [Module.Flat O M]
    (hcl : ClosedClass (fun (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N) =>
      Admissible PD emb Γ t Ut π))
    (hW : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], Admissible PD emb Γ t Ut (coefRep W X))
    (hχ : ∀ a : ℕ, Admissible PD emb Γ t Ut
      (twistRep (Representation.trivial O G (O ⧸ Ideal.span {Γ.lam ^ a})) Γ.χ₁))
    (hnil : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, 1 ≤ a ∧ ∀ x : X, Γ.lam ^ a • x = 0)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] :
    (∃ A : Submodule O (H1 (twCoef W Γ.χ₁ X) ⊤), adm PD emb Γ t Ut W X = A) ∧
    (∀ (a : ℕ) (ha : ∀ x : X, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ t Ut W X = admAt PD emb Γ t Ut W X a ha) ∧
    ∀ (X' : Type) [AddCommGroup X'] [Module O X'] [Finite X'] (f : X →ₗ[O] X') (c : H1 (twCoef W Γ.χ₁ X) ⊤),
      (c ∈ adm PD emb Γ t Ut W X → coefH1 W Γ.χ₁ f c ∈ adm PD emb Γ t Ut W X') ∧
      (Function.Injective f → coefH1 W Γ.χ₁ f c ∈ adm PD emb Γ t Ut W X' → c ∈ adm PD emb Γ t Ut W X) := by
  have hT := hcl.twist Γ.χ₁
  have hπ : ∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Finite Y],
      Admissible PD emb Γ t Ut (twistRep (twCoef W Γ.χ₁ Y) Γ.χ₁) := fun Y _ _ _ => by
    rw [twist_twCoef]
    exact hW Y

  have hlev : ∀ (a : ℕ) (ha : ∀ x : X, Γ.lam ^ a • x = 0), 1 ≤ a →
      adm PD emb Γ t Ut W X = admAt PD emb Γ t Ut W X a ha := fun a ha h1a =>
    Set.ext fun c => ⟨fun ⟨_, ha', _, hc⟩ => mem_admAt_of_mem_admAt hcl hW hχ X ha' ha hc,
      fun hc => ⟨a, ha, h1a, hc⟩⟩
  obtain ⟨a, h1a, ha⟩ := hnil X
  have hzero : (0 : H1 (twCoef W Γ.χ₁ X) ⊤) ∈ adm PD emb Γ t Ut W X := by
    rw [hlev a ha h1a, ← Submodule.Quotient.mk_zero, mk_mem_admissibleAt_iff_cocycle]
    exact hT.zero (smul_tensor_eq_zero ha) (hπ X) (hχ a)
  have hadd : ∀ {x y : H1 (twCoef W Γ.χ₁ X) ⊤}, x ∈ adm PD emb Γ t Ut W X → y ∈ adm PD emb Γ t Ut W X →
      x + y ∈ adm PD emb Γ t Ut W X := by
    intro x y hx hy
    rw [hlev a ha h1a] at hx hy ⊢
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [mk_mem_admissibleAt_iff_cocycle] at hx hy
    rw [← Submodule.Quotient.mk_add, mk_mem_admissibleAt_iff_cocycle]
    exact hT.add (smul_tensor_eq_zero ha) z z' hx hy (hπ X)
  have hsmul : ∀ (r : O) {x : H1 (twCoef W Γ.χ₁ X) ⊤}, x ∈ adm PD emb Γ t Ut W X →
      r • x ∈ adm PD emb Γ t Ut W X := by
    intro r x hx
    rw [hlev a ha h1a] at hx ⊢
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mk_mem_admissibleAt_iff_cocycle] at hx
    rw [← Submodule.Quotient.mk_smul, mk_mem_admissibleAt_iff_cocycle]
    exact hT.push (dvd_refl _) (smul_tensor_eq_zero ha) (smul_tensor_eq_zero ha) (r • LinearMap.id)
      (fun σ x => by simp) z (r • z) (fun _ => rfl) hx (hπ X)
  refine ⟨⟨{ carrier := _, add_mem' := hadd, zero_mem' := hzero, smul_mem' := hsmul }, rfl⟩, hlev, ?_⟩
  · intro X' _ _ _ f c
    obtain ⟨b, h1b, hb⟩ := hnil (X × X')
    have hbX : ∀ x : X, Γ.lam ^ b • x = 0 := fun x => by
      simpa using congrArg Prod.fst (hb (x, 0))
    have hbX' : ∀ x : X', Γ.lam ^ b • x = 0 := fun x => by
      simpa using congrArg Prod.snd (hb (0, x))
    have hlev' : adm PD emb Γ t Ut W X' = admAt PD emb Γ t Ut W X' b hbX' :=
      Set.ext fun c => ⟨fun ⟨_, ha', _, hc⟩ => mem_admAt_of_mem_admAt hcl hW hχ X' ha' hbX' hc,
        fun hc => ⟨b, hbX', h1b, hc⟩⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨z', hz'c, hz'⟩ := exists_coefH1_mk Γ.χ₁ f z
    rw [hlev b hbX h1b, hlev', hz'c, mk_mem_admissibleAt_iff_cocycle, mk_mem_admissibleAt_iff_cocycle]
    refine ⟨fun hz => hT.push (dvd_refl _) (smul_tensor_eq_zero hbX) (smul_tensor_eq_zero hbX')
      (f.lTensor M) (fun σ x => lTensor_twCoef Γ.χ₁ f σ x) z z' hz' hz (hπ X'), fun hi hz => ?_⟩
    exact hT.pull (dvd_refl _) (smul_tensor_eq_zero hbX) (smul_tensor_eq_zero hbX') (f.lTensor M)
      (fun σ x => lTensor_twCoef Γ.χ₁ f σ x) (Module.Flat.lTensor_preserves_injective_linearMap f hi)
      z z' hz' hz (hχ b)

theorem admissible_of_twist_trivial_tensor {X : Type} [AddCommGroup X] [Module O X]
    (h : Admissible PD emb Γ t Ut (coefRep (Γ.Wchi 1) X)) :
    Admissible PD emb Γ t Ut (twistRep (Representation.trivial O G X) Γ.χ₁) := by
  refine Admissible.of_equiv h (TensorProduct.lid O X) (fun g m => ?_)
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [GalData.Wchi, coefRep_tmul, TensorProduct.lid_tmul, Formalism.GaloisCohomology.scalRep_apply, GalData.chi_one,
      twistRep_apply, Representation.trivial_apply, smul_eq_mul, mul_smul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end Classes

theorem not_isUnit_prime (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O]
    [Algebra.IsIntegral ℤ_[l] O] (hi : Function.Injective (algebraMap ℤ_[l] O)) : ¬ IsUnit ((l : ℕ) : O) := by
  intro hu
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := O)
    (IsLocalRing.maximalIdeal ℤ_[l]) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]; exact bot_le)
  have hmem : ((l : ℕ) : ℤ_[l]) ∈ Q.comap (algebraMap ℤ_[l] O) := by
    rw [hQc]
    exact (IsLocalRing.mem_maximalIdeal _).mpr PadicInt.p_nonunit
  rw [Ideal.mem_comap, map_natCast] at hmem
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)

open GlobalTheory.PhiGam GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem not_isUnit_integers (l : ℕ) [Fact l.Prime] (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  obtain ⟨⟨hD, hV, -⟩, hfd, -, -, -, -⟩ := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have := hD
  have := hV
  have := hfd

  have hunit : ∀ b : ℤ_[l], b ≠ 0 → IsUnit (algebraMap ℤ_[l] ↥(OL LL) b) := by
    intro b hb
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb PadicInt.irreducible_p
    rw [map_mul, map_pow, map_natCast]
    exact (u.isUnit.map _).mul (hu.pow k)

  have hmem : ∀ x : ℚ_[l], algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbQ : algebraMap ℤ_[l] ℚ_[l] b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hb0
    obtain ⟨v, hv⟩ := hunit b hb0
    have key : algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] a / algebraMap ℤ_[l] ℚ_[l] b) =
        ((algebraMap ℤ_[l] ↥(OL LL) a * ↑v⁻¹ : ↥(OL LL)) : ↥LL.1) := by
      refine mul_right_cancel₀ ((map_ne_zero (algebraMap ℚ_[l] ↥LL.1)).mpr hbQ) ?_
      rw [← map_mul, div_mul_cancel₀ _ hbQ, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      have e2 : algebraMap ℤ_[l] ↥LL.1 b = ((algebraMap ℤ_[l] ↥(OL LL) b : ↥(OL LL)) : ↥LL.1) := rfl
      have e3 : algebraMap ℤ_[l] ↥LL.1 a = ((algebraMap ℤ_[l] ↥(OL LL) a : ↥(OL LL)) : ↥LL.1) := rfl
      rw [e2, e3, ← hv]
      norm_cast
      rw [mul_assoc, Units.inv_mul, mul_one]
    rw [key]
    exact Subtype.property _

  let A : Subalgebra ℚ_[l] ↥LL.1 := { (OL LL).toSubsemiring with algebraMap_mem' := hmem }
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hinv : (ϖ : ↥LL.1)⁻¹ ∈ OL LL :=
    A.inv_mem_of_algebraic (x := ⟨ϖ, ϖ.2⟩) (Algebra.IsAlgebraic.isAlgebraic _)
  have hne : (ϖ : ↥LL.1) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  exact hϖ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩)

theorem adm_classes_of_flat {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (hC : S.Closed) (hA : S.StdAdm)
    {M : Type} [AddCommGroup M] [Module S.O M] [Module.Flat S.O M] (W : Representation S.O S.G M)
    (hW : S.CoefAdm W) : S.Lem0 W := by
  have hcl : ClosedClass (O := S.O) (G := S.G)
      (fun (N : Type) [AddCommGroup N] [Module S.O N] (π : Representation S.O S.G N) => S.admitted π) :=
    { sub := fun f hf hi ha => ((hC _ _ _ _).1 f hf).1 hi ha
      quot := fun f hf hs ha => ((hC _ _ _ _).1 f hf).2 hs ha
      prod := fun ha hb => (hC _ _ _ _).2 ha hb }
  obtain ⟨⟨hD, hV, -⟩, -, -, -, -, -⟩ := (GlobalTheory.LocalIntegers.good_integers l S.LL).1
  have := hD
  have := hV
  have hl : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  have hfin : ∀ a : ℕ, Finite (S.O ⧸ Ideal.span {S.Γ.lam ^ a}) := fun a => by
    have := (GlobalTheory.LocalIntegers.good_integers l S.LL).2 a
    exact finite_quot_pow hl (not_isUnit_integers l S.LL) a
  have hχ : ∀ a : ℕ, S.admitted (twistRep (Representation.trivial S.O S.G (S.O ⧸ Ideal.span {S.Γ.lam ^ a})) S.Γ.χ₁) :=
    fun a => by
      have := hfin a
      exact admissible_of_twist_trivial_tensor (hA.2 1 le_rfl S.D.one_le_letterBlockLength _)
  intro X _ _ _
  exact admissible_classes_props_of_flat_coefficient hcl hW hχ (fun Y _ _ _ => exists_pow_smul_eq_zero hl Y) X

theorem admissibleLocalSituation_admissible_classes : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Closed → S.StdAdm →
    S.Lem0 S.Γ.W₀ ∧ ∀ c : ℕ, 1 ≤ c → c ≤ S.D.t → S.Lem0 (S.Γ.Wchi c) := by
  intro l _ P S hC hA
  refine ⟨?_, fun c h1 h2 => adm_classes_of_flat S hC hA (S.Γ.Wchi c) (hA.2 c h1 h2)⟩
  have : Module.Free S.O ↥S.Γ.T₀.L.T := S.Γ.T₀.L.free
  exact adm_classes_of_flat S hC hA S.Γ.W₀ hA.1

end GlobalTheory.AdmClasses
