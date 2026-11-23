import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtTensorAlt
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBaseChangeCons

theorem tensor_ringHom_ext {R S B C : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R B] (φ ψ : S ⊗[R] B →+* C)
    (h₁ : ∀ s : S, φ (s ⊗ₜ[R] (1 : B)) = ψ (s ⊗ₜ[R] (1 : B)))
    (h₂ : ∀ b : B, φ ((1 : S) ⊗ₜ[R] b) = ψ ((1 : S) ⊗ₜ[R] b)) : φ = ψ := by
  first
  | exact @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor
  | exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor
  | (apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorRingHomExtensionality.ringHom_ext_tensor ..)

theorem one_tmul_algebraMap {R S B : Type} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] (r : R) :
    (1 : S) ⊗ₜ[R] algebraMap R B r = algebraMap R S r ⊗ₜ[R] (1 : B) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem sub_C_coeff_mem {R : Type} [CommRing R] (p : Polynomial R) :
    p - C (p.coeff 0) ∈ Ideal.span {(X : Polynomial R)} :=
  Ideal.mem_span_singleton.mpr X_dvd_sub_C

theorem mem_originIdeal_iff {R : Type} [CommRing R] [IsLocalRing R] (f : Polynomial R) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal R ↔ f.coeff 0 ∈ maximalIdeal R := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal R ≤ (maximalIdeal R).comap (constantCoeff (R := R)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa [Ideal.mem_comap] using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp [Ideal.mem_comap]
    simpa [Ideal.mem_comap] using hle hf
  · intro hf
    have h1 : C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal R :=
      Ideal.mem_sup_right (sub_C_coeff_mem f)
    simpa using Ideal.add_mem _ h2 h1

theorem comap_maximalIdeal_eq_originIdeal {T O A₁ : Type} [CommRing T] [IsLocalRing T] [CommRing O]
    [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    [IsLocalHom (algebraMap T O)] (hXO : algebraMap (Polynomial T) O X ∈ maximalIdeal O)
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T) [IsLocalHom i₁] :
    (maximalIdeal O).comap ((algebraMap (Polynomial T) O).comp (mapRingHom i₁)) =
      GlobalTheory.KeyOriginCut.originIdeal A₁ := by
  ext p
  rw [Ideal.mem_comap, mem_originIdeal_iff, RingHom.comp_apply, coe_mapRingHom]
  set q := p.map i₁
  have hsplit : algebraMap (Polynomial T) O q =
      algebraMap (Polynomial T) O (q - C (q.coeff 0)) + algebraMap T O (q.coeff 0) := by
    rw [map_sub, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq]; ring
  have hX : algebraMap (Polynomial T) O (q - C (q.coeff 0)) ∈ maximalIdeal O := by
    obtain ⟨r, hr⟩ := (X_dvd_sub_C (p := q))
    rw [hr, map_mul]
    exact Ideal.mul_mem_right _ _ hXO
  rw [hsplit]
  constructor
  · intro h
    have h' : algebraMap T O (q.coeff 0) ∈ maximalIdeal O := by
      have := Ideal.sub_mem _ h hX
      simpa using this
    rw [mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map,
      mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal] at h'
    exact h'
  · intro h
    refine Ideal.add_mem _ hX ?_
    rw [mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal, coeff_map,
      mem_maximalIdeal, map_mem_nonunits_iff, ← mem_maximalIdeal]
    exact h

theorem exists_mul_mem_span_X {A EA : Type} [CommRing A] [IsNoetherianRing A] [CommRing EA]
    [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA] (QA : Ideal EA) [QA.IsPrime]
    (ρ : Localization.AtPrime QA →+* A)
    (hker : RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) X}) :
    ∃ s ∉ QA, ∀ e : EA, ρ (algebraMap EA (Localization.AtPrime QA) e) = 0 →
      s * e ∈ Ideal.span {algebraMap (Polynomial A) EA X} := by
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  set L := Localization.AtPrime QA
  set I := RingHom.ker (ρ.comp (algebraMap EA L))
  set N := Ideal.span {algebraMap (Polynomial A) EA X}
  have key : ∀ (J : Ideal EA) (hJ : J.FG), J ≤ I → ∃ s ∉ QA, ∀ e ∈ J, s * e ∈ N := by
    intro J hJ
    induction J, hJ using Submodule.fg_induction with
    | singleton x =>
      intro hx
      have hxI : x ∈ I := hx (Submodule.mem_span_singleton_self x)
      have hk : algebraMap EA L x ∈ RingHom.ker ρ := hxI
      rw [hker, Ideal.mem_span_singleton'] at hk
      obtain ⟨a, ha⟩ := hk
      obtain ⟨⟨y, m⟩, hy⟩ := IsLocalization.surj QA.primeCompl a
      have he : algebraMap EA L (y * algebraMap (Polynomial A) EA X) =
          algebraMap EA L (m * x) := by
        rw [map_mul, map_mul, ← ha, ← IsScalarTower.algebraMap_apply, ← hy]
        simp only at *
        ring
      obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists QA.primeCompl L).mp he
      refine ⟨u * m, (u * m).2, ?_⟩
      intro e hex
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hex
      have : (u : EA) * (y * algebraMap (Polynomial A) EA X) ∈ N :=
        Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
      rw [hu] at this
      have h2 := Ideal.mul_mem_left N c this
      rw [smul_eq_mul]
      convert h2 using 1
      push_cast
      ring
    | sup J₁ J₂ _ _ h₁ h₂ =>
      intro hle
      obtain ⟨s₁, hs₁, H₁⟩ := h₁ (le_trans le_sup_left hle)
      obtain ⟨s₂, hs₂, H₂⟩ := h₂ (le_trans le_sup_right hle)
      refine ⟨s₁ * s₂, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs₁ hs₂, ?_⟩
      intro e he
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp he
      rw [mul_add]
      refine N.add_mem ?_ ?_
      · have := N.mul_mem_left s₂ (H₁ y hy)
        convert this using 1; ring
      · have := N.mul_mem_left s₁ (H₂ z hz)
        convert this using 1; ring
  obtain ⟨s, hs, H⟩ := key I (IsNoetherian.noetherian I) le_rfl
  exact ⟨s, hs, fun e he => H e he⟩

end GlobalTheory.KeyOriginBaseChangeCons

namespace GlobalTheory.KeyOriginBaseChangeCons

theorem exists_baseChange_retract : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (ρ : Localization.AtPrime QA →+* A),
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (γ₀ : EA →+* EA₁) (γ : Localization.AtPrime QA →+* Localization.AtPrime QA₁) (ρ' : EA₁ →+* A₁),
      QA₁.comap (algebraMap (Polynomial A₁) EA₁) = GlobalTheory.KeyOriginCut.originIdeal A₁ ∧
      jA₁.comp (algebraMap (Polynomial A₁) (Localization.AtPrime QA₁)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i₁) ∧
      jA₁.comp γ = jA ∧
      γ.comp (algebraMap EA (Localization.AtPrime QA)) = (algebraMap EA₁ (Localization.AtPrime QA₁)).comp γ₀ ∧
      γ.comp (algebraMap A (Localization.AtPrime QA)) = (algebraMap A₁ (Localization.AtPrime QA₁)).comp j ∧
      ρ'.comp γ₀ = j.comp (ρ.comp (algebraMap EA (Localization.AtPrime QA))) ∧
      ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ ∧
      ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 ∧
      (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
        Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) ∧
      (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) := by
  intro T O _ _ _ _ _ _ _ _ hTO hXO A _ _ _ _ i EA _ _ _ _ _ QA _ jA ρ hQA hjA hρ A₁ _ _ _ j i₁ hi₁ hloc hij
  haveI := hTO
  haveI := hloc
  letI algP : Algebra (Polynomial A) (Polynomial A₁) := (mapRingHom j).toAlgebra
  letI algO : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (mapRingHom i)).toAlgebra
  set L := Localization.AtPrime QA with hL

  have hρpoly : ρ.comp (algebraMap (Polynomial A) L) = evalRingHom 0 := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · rw [RingHom.comp_apply, ← algebraMap_eq (R := A), ← IsScalarTower.algebraMap_apply,
        ← RingHom.comp_apply ρ, hρ.1, algebraMap_eq]
      simp
    · have hx : algebraMap (Polynomial A) L X ∈ RingHom.ker ρ := by
        rw [hρ.2.1]; exact Ideal.mem_span_singleton_self _
      rw [RingHom.comp_apply, RingHom.mem_ker.mp hx]; simp
  let f₁ : Polynomial A₁ →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (mapRingHom i₁)
      commutes' := fun r => by
        show algebraMap (Polynomial T) O (mapRingHom i₁ (mapRingHom j r)) =
          algebraMap (Polynomial T) O (mapRingHom i r)
        rw [coe_mapRingHom, coe_mapRingHom, coe_mapRingHom, Polynomial.map_map, hij] }
  let f₂ : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA L)
      commutes' := fun r => by
        show jA (algebraMap EA L (algebraMap (Polynomial A) EA r)) =
          algebraMap (Polynomial T) O (mapRingHom i r)
        rw [← IsScalarTower.algebraMap_apply (Polynomial A) EA L r]
        exact congrArg (fun φ => φ r) hjA }
  let EA₁ := TensorProduct (Polynomial A) (Polynomial A₁) EA
  let g : EA₁ →+* O := (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hg : ∀ p e, g (p ⊗ₜ[Polynomial A] e) = algebraMap (Polynomial T) O (p.map i₁) * jA (algebraMap EA L e) :=
    fun p e => Algebra.TensorProduct.lift_tmul _ _ _ p e
  letI iA1 : Algebra A₁ EA₁ := ((algebraMap (Polynomial A₁) EA₁).comp C).toAlgebra
  have hmapP : ∀ p : Polynomial A₁, algebraMap (Polynomial A₁) EA₁ p = p ⊗ₜ[Polynomial A] (1 : EA) := by
    intro p; rw [Algebra.TensorProduct.algebraMap_apply]; rfl
  have hAP : ∀ a : A₁, algebraMap A₁ EA₁ a = algebraMap (Polynomial A₁) EA₁ (C a) := fun a => rfl
  have hmapA : ∀ a : A₁, algebraMap A₁ EA₁ a = C a ⊗ₜ[Polynomial A] (1 : EA) := fun a => hmapP (C a)
  let γ₀ : EA →+* EA₁ := (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] EA₁).toRingHom
  have hγ₀ : ∀ e, γ₀ e = (1 : Polynomial A₁) ⊗ₜ[Polynomial A] e := fun e => rfl
  have hγ₀A : ∀ a : A, γ₀ (algebraMap A EA a) = algebraMap A₁ EA₁ (j a) := by
    intro a
    rw [hγ₀, hmapA, IsScalarTower.algebraMap_apply A (Polynomial A) EA, one_tmul_algebraMap, algebraMap_eq]
    show (mapRingHom j (C a)) ⊗ₜ[Polynomial A] (1 : EA) = _
    rw [coe_mapRingHom, Polynomial.map_C]
  have hγ₀X : γ₀ (algebraMap (Polynomial A) EA X) = algebraMap (Polynomial A₁) EA₁ X := by
    rw [hγ₀, hmapP, one_tmul_algebraMap]
    show (mapRingHom j X) ⊗ₜ[Polynomial A] (1 : EA) = _
    rw [coe_mapRingHom, Polynomial.map_X]
  have hgP : ∀ p, g (algebraMap (Polynomial A₁) EA₁ p) = algebraMap (Polynomial T) O (p.map i₁) := by
    intro p; rw [hmapP, hg, map_one, map_one, mul_one]
  have hgγ : ∀ e, g (γ₀ e) = jA (algebraMap EA L e) := by
    intro e; rw [hγ₀, hg, Polynomial.map_one, map_one, one_mul]
  let QA₁ : Ideal EA₁ := (maximalIdeal O).comap g
  have hunit : ∀ y : EA₁, y ∉ QA₁ → IsUnit (g y) := by
    intro y hy
    by_contra h
    exact hy ((mem_maximalIdeal _).2 h)
  let L₁ := Localization.AtPrime QA₁
  let jA₁ : L₁ →+* O := IsLocalization.lift (M := QA₁.primeCompl) (g := g) (fun y => hunit y y.2)
  have hjA₁ : ∀ x, jA₁ (algebraMap EA₁ L₁ x) = g x := fun x => IsLocalization.lift_eq _ x
  have hγ₀Q : ∀ e : EA, e ∉ QA → γ₀ e ∉ QA₁ := by
    intro e he h
    have h1 : g (γ₀ e) ∈ maximalIdeal O := h
    rw [hgγ] at h1
    have hu : IsUnit (algebraMap EA L e) := IsLocalization.map_units L (⟨e, he⟩ : QA.primeCompl)
    exact (mem_maximalIdeal _).1 h1 (hu.map jA)
  let γ : L →+* L₁ := IsLocalization.lift (M := QA.primeCompl) (g := (algebraMap EA₁ L₁).comp γ₀)
    (fun y => IsLocalization.map_units L₁ (⟨γ₀ y, hγ₀Q y y.2⟩ : QA₁.primeCompl))
  have hγ : ∀ e, γ (algebraMap EA L e) = algebraMap EA₁ L₁ (γ₀ e) := fun e => IsLocalization.lift_eq _ e
  have hρA : ∀ b : A, ρ (algebraMap EA L (algebraMap A EA b)) = b := by
    intro b; rw [← IsScalarTower.algebraMap_apply A EA L b]; exact congrArg (fun φ => φ b) hρ.1
  let Xs : Ideal (Polynomial A₁) := Ideal.span {X}
  let φ0 : Polynomial A₁ ⧸ Xs →+* A₁ := Ideal.Quotient.lift Xs (evalRingHom 0) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp)
  have hφ0 : ∀ p, φ0 (Ideal.Quotient.mk Xs p) = eval 0 p := fun p => Ideal.Quotient.lift_mk _ _ _
  let r₁ : Polynomial A₁ →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs := Ideal.Quotient.mkₐ (Polynomial A) Xs
  let r₂ : EA →ₐ[Polynomial A] Polynomial A₁ ⧸ Xs :=
    { toRingHom := (Ideal.Quotient.mk Xs).comp (C.comp (j.comp (ρ.comp (algebraMap EA L))))
      commutes' := fun r => by
        show Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L (algebraMap (Polynomial A) EA r))))) =
          Ideal.Quotient.mk Xs (mapRingHom j r)
        rw [← IsScalarTower.algebraMap_apply (Polynomial A) EA L r, ← RingHom.comp_apply ρ, hρpoly,
          Ideal.Quotient.eq, coe_mapRingHom, coe_evalRingHom, ← coeff_zero_eq_eval_zero]
        have : C (j (r.coeff 0)) - r.map j = -((r.map j) - C ((r.map j).coeff 0)) := by
          rw [coeff_map]; ring
        rw [this]
        exact Xs.neg_mem (sub_C_coeff_mem _) }
  let ρ' : EA₁ →+* A₁ := φ0.comp (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _)).toRingHom
  have hρ' : ∀ p e, ρ' (p ⊗ₜ[Polynomial A] e) = eval 0 p * j (ρ (algebraMap EA L e)) := by
    intro p e
    show φ0 (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _) (p ⊗ₜ[Polynomial A] e)) = _
    rw [Algebra.TensorProduct.lift_tmul, map_mul]
    show φ0 (Ideal.Quotient.mk Xs p) * φ0 (Ideal.Quotient.mk Xs (C (j (ρ (algebraMap EA L e))))) = _
    rw [hφ0, hφ0, eval_C]
  have hρ'P : ∀ p, ρ' (algebraMap (Polynomial A₁) EA₁ p) = eval 0 p := by
    intro p; rw [hmapP, hρ']; simp only [map_one, mul_one]
  have hρ'γ : ∀ e, ρ' (γ₀ e) = j (ρ (algebraMap EA L e)) := by
    intro e; rw [hγ₀, hρ', eval_one, one_mul]
  have hρ'A : ∀ a, ρ' (algebraMap A₁ EA₁ a) = a := by
    intro a
    show ρ' (algebraMap (Polynomial A₁) EA₁ (C a)) = a
    rw [hρ'P, eval_C]
  have hcong : ∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ L₁ x) ∈
      Ideal.span {algebraMap (Polynomial T) O X} := by
    set I := Ideal.span {algebraMap (Polynomial T) O X}
    have hext : (Ideal.Quotient.mk I).comp ((algebraMap T O).comp (i₁.comp ρ')) =
        (Ideal.Quotient.mk I).comp g := by
      apply tensor_ringHom_ext
      · intro p
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hmapP p, hρ'P, hgP, IsScalarTower.algebraMap_apply T (Polynomial T) O, algebraMap_eq, ← map_sub]
        have : C (i₁ (eval 0 p)) - p.map i₁ = -((p.map i₁) - C ((p.map i₁).coeff 0)) := by
          rw [coeff_map, coeff_zero_eq_eval_zero]; ring
        rw [this, map_neg]
        exact I.neg_mem (Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C))
      · intro e
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hγ₀ e, hρ'γ, hgγ, ← RingHom.comp_apply i₁ j, hij]
        exact hρ.2.2 _
    intro x
    rw [hjA₁, ← Ideal.Quotient.eq]
    exact congrArg (fun φ => φ x) hext
  obtain ⟨s₀, hs₀, Hs₀⟩ := exists_mul_mem_span_X QA ρ hρ.2.1
  have hker : ∀ x : EA₁, ρ' x = 0 →
      ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ X} := by
    set N₁ := Ideal.span {algebraMap (Polynomial A₁) EA₁ X}
    set Ik := RingHom.ker (ρ.comp (algebraMap EA L))
    set J := N₁ ⊔ Ik.map γ₀
    have hext : (Ideal.Quotient.mk J).comp ((algebraMap A₁ EA₁).comp ρ') = Ideal.Quotient.mk J := by
      apply tensor_ringHom_ext
      · intro p
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hmapP p, hρ'P, hAP, ← map_sub]
        have : C (eval 0 p) - p = -(p - C (p.coeff 0)) := by rw [coeff_zero_eq_eval_zero]; ring
        rw [this, map_neg]
        refine J.neg_mem (Ideal.mem_sup_left ?_)
        exact Ideal.mem_span_singleton.mpr (map_dvd _ X_dvd_sub_C)
      · intro e
        simp only [RingHom.comp_apply]
        rw [Ideal.Quotient.eq]
        rw [← hγ₀ e, hρ'γ, ← hγ₀A, ← map_sub]
        refine Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_)
        rw [RingHom.mem_ker, RingHom.comp_apply, map_sub, map_sub, hρA, sub_self]
    intro x hx
    have hxJ : x ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← congrArg (fun φ => φ x) hext]
      simp [hx]
    refine ⟨γ₀ s₀, hγ₀Q s₀ hs₀, ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxJ
    rw [mul_add]
    refine N₁.add_mem (N₁.mul_mem_left _ hy) ?_
    have h1 : Ideal.span {γ₀ s₀} * Ik.map γ₀ = (Ideal.span {s₀} * Ik).map γ₀ := by
      rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
    have h2 : Ideal.span {s₀} * Ik ≤ Ideal.span {algebraMap (Polynomial A) EA X} := by
      rw [Ideal.span_singleton_mul_le_iff]
      intro w hw; exact Hs₀ w (RingHom.mem_ker.mp hw)
    have h3 : (Ideal.span {algebraMap (Polynomial A) EA X}).map γ₀ = N₁ := by
      rw [Ideal.map_span, Set.image_singleton, hγ₀X]
    have h4 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (γ₀ s₀)) hz
    rw [h1] at h4
    exact h3 ▸ Ideal.map_mono h2 h4
  refine ⟨EA₁, inferInstance, inferInstance, iA1, IsScalarTower.of_algebraMap_eq (fun x => ?_),
    inferInstance, QA₁, inferInstance, jA₁, γ₀, γ, ρ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcong, hker⟩
  · show algebraMap (Polynomial A₁) EA₁ (C x) = algebraMap (Polynomial A₁) EA₁ (algebraMap A₁ (Polynomial A₁) x)
    rw [algebraMap_eq]
  · rw [← comap_maximalIdeal_eq_originIdeal hXO i₁]
    ext p
    show g (algebraMap _ EA₁ p) ∈ maximalIdeal O ↔ _
    rw [Ideal.mem_comap, hgP]; rfl
  · refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ L₁, hjA₁, hgP]; rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun e => ?_)
    simp only [RingHom.comp_apply]
    rw [hγ, hjA₁, hgγ]
  · exact RingHom.ext fun e => hγ e
  · refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A EA L, hγ, hγ₀A, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply A₁ EA₁ L₁]
  · exact RingHom.ext fun e => hρ'γ e
  · exact RingHom.ext fun a => hρ'A a
  · rw [hρ'P, eval_X]

end GlobalTheory.KeyOriginBaseChangeCons
