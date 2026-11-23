import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeConj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Win.T2.TypeConj

open GlobalTheory.PRep

section General

variable {G V V' W W' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private def Cj (γ : ℂ ≃+* ℂ) (π : Representation ℂ G V) (π' : Representation ℂ G V') (f : V ≃+ V') : Prop :=
  (∀ (z : ℂ) v, f (z • v) = γ z • f v) ∧ ∀ g v, f (π g v) = π' g (f v)

private theorem Cj.symm {γ : ℂ ≃+* ℂ} {π : Representation ℂ G V} {π' : Representation ℂ G V'} {f : V ≃+ V'}
    (h : Cj γ π π' f) : Cj γ.symm π' π f.symm :=
  ⟨fun z v => f.injective (by rw [h.1]; simp), fun g v => f.injective (by rw [h.2]; simp)⟩

private def Cj.pull {γ : ℂ ≃+* ℂ} {π : Representation ℂ G V} {π' : Representation ℂ G V'} {f : V ≃+ V'}
    (h : Cj γ π π' f) (S : Subrepresentation π') : Subrepresentation π :=
  ⟨{ carrier := {v | f v ∈ S.toSubmodule}
     add_mem' := fun {a b} ha hb => by
       show f (a + b) ∈ S.toSubmodule
       rw [map_add]; exact add_mem ha hb
     zero_mem' := by
       show f 0 ∈ S.toSubmodule
       rw [map_zero]; exact zero_mem _
     smul_mem' := fun c a ha => by
       show f (c • a) ∈ S.toSubmodule
       rw [h.1]; exact Submodule.smul_mem _ _ ha }, fun g v hv => by
     show f (π g v) ∈ S.toSubmodule
     rw [h.2]; exact S.apply_mem_toSubmodule g hv⟩

private def Cj.iso {γ : ℂ ≃+* ℂ} {π : Representation ℂ G V} {π' : Representation ℂ G V'} {f : V ≃+ V'}
    (h : Cj γ π π' f) : Subrepresentation π' ≃o Subrepresentation π where
  toFun := h.pull
  invFun := h.symm.pull
  left_inv S := SetLike.ext fun v => by
    show f (f.symm v) ∈ S.toSubmodule ↔ v ∈ S.toSubmodule
    rw [f.apply_symm_apply]
  right_inv S := SetLike.ext fun v => by
    show f.symm (f v) ∈ S.toSubmodule ↔ v ∈ S.toSubmodule
    rw [f.symm_apply_apply]
  map_rel_iff' {S T} := ⟨fun H v hv => by
    obtain ⟨v, rfl⟩ := f.surjective v
    exact H (show v ∈ h.pull S from hv), fun H v hv => H hv⟩

private theorem cosocle_conj {γ : ℂ ≃+* ℂ} {π : Representation ℂ G V} {π' : Representation ℂ G V'} {F : V ≃+ V'}
    {σ : Representation ℂ G W} {σ' : Representation ℂ G W'} {f : W ≃+ W'} (hF : Cj γ π π' F) (hf : Cj γ σ σ' f)
    (hi : σ'.IsIrreducible) (h : IsCosocle σ π) : IsCosocle σ' π' := by
  obtain ⟨-, p, hp, hS⟩ := h
  let q : π'.IntertwiningMap σ' :=
    { toFun := fun v => f (p (F.symm v))
      map_add' := fun a b => by simp only [map_add]
      map_smul' := fun c a => by rw [hF.symm.1, map_smul, hf.1]; simp
      isIntertwining' := fun g => LinearMap.ext fun v => by
        show f (p (F.symm (π' g v))) = σ' g (f (p (F.symm v)))
        rw [hF.symm.2, p.isIntertwining, hf.2] }
  refine ⟨hi, q, f.surjective.comp (hp.comp F.symm.surjective), fun S h => hF.iso.injective ?_⟩
  rw [hS _ ((OrderIso.isCoatom_iff _ _).2 h)]
  refine SetLike.ext fun y => ?_
  show p y = 0 ↔ f (p (F.symm (F y))) = 0
  simp

private theorem cosocle_move {π : Representation ℂ G V} {σ : Representation ℂ G W} {χ ψ : G →* ℂˣ}
    (h : IsCosocle (twist σ ψ) π) (e : χ * ψ = 1) : IsCosocle σ (twist π χ) := by
  have h1 := h.twist χ
  rwa [twist_twist, e, twist_one] at h1

private theorem cosocle_move' {π : Representation ℂ G V} {σ : Representation ℂ G W} {χ ψ : G →* ℂˣ}
    (h : IsCosocle σ (twist π χ)) (e : χ * ψ = 1) : IsCosocle (twist σ ψ) π := by
  have h1 := h.twist ψ
  rwa [twist_twist, mul_comm, e, twist_one] at h1

variable [TopologicalSpace G] [IsTopologicalGroup G]

private def indMap {γ : ℂ ≃+* ℂ} {P : Subgroup G} {σ : Representation ℂ P V} {τ : Representation ℂ P W} {j : V ≃+ W}
    (h : Cj γ σ τ j) (φ : smoothPart (ind P σ)) : smoothPart (ind P τ) :=
  ⟨⟨fun g => j (φ.1.1 g), fun p g => by
      show j (φ.1.1 (p * g)) = τ p (j (φ.1.1 g))
      rw [φ.1.2 p g, h.2]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds φ.2 (by simp)) fun g hg => by
      have hg' : ind P σ g φ.1 = φ.1 := hg
      apply Subtype.ext
      funext x
      exact congrArg j (congrFun (congrArg Subtype.val hg') x))⟩

private theorem smInd_conj {γ : ℂ ≃+* ℂ} {P : Subgroup G} {σ : Representation ℂ P V} {τ : Representation ℂ P W}
    {j : V ≃+ W} (h : Cj γ σ τ j) : ∃ F, Cj γ (smInd P σ) (smInd P τ) F :=
  ⟨{ toFun := indMap h
     invFun := indMap h.symm
     left_inv := fun φ => Subtype.ext (Subtype.ext (funext fun x => j.symm_apply_apply _))
     right_inv := fun φ => Subtype.ext (Subtype.ext (funext fun x => j.apply_symm_apply _))
     map_add' := fun φ ψ => Subtype.ext (Subtype.ext (funext fun x => map_add j _ _)) },
   fun z φ => Subtype.ext (Subtype.ext (funext fun x => h.1 _ _)), fun g φ => rfl⟩

end General

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private def cj {Γ : Type} [Group Γ] (γ : ℂ ≃+* ℂ) (χ : Γ →* ℂˣ) : Γ →* ℂˣ := (Units.map (γ : ℂ →* ℂ)).comp χ

private theorem cj_val {Γ : Type} [Group Γ] (γ : ℂ ≃+* ℂ) (χ : Γ →* ℂˣ) (g : Γ) : (cj γ χ g : ℂ) = γ (χ g) := rfl

private theorem cj_abs (γ : ℂ ≃+* ℂ) (m : ℕ) (x : kˣ) : γ (absPow k m x) = absPow k m x := by
  rw [val_absPow, Complex.cpow_natCast, GlobalTheory.LGrp.nabs_eq_zpow]
  simp

private theorem cj_smooth (γ : ℂ ≃+* ℂ) {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmoothChar (cj γ χ) :=
  Subgroup.isOpen_mono (H₁ := χ.ker) (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [cj, hg]) h

private theorem prod_conj (γ : ℂ ≃+* ℂ) {n : ℕ} (e : (Σ _ : Fin n, Fin 1) ≃ Fin n) (ω : Fin n → kˣ →* ℂˣ) :
    ∃ F, Cj γ (multiProd e fun a => detRep (Fin 1) (ω a * absPow k (((n : ℂ) - 1) / 2)))
      (multiProd e fun a => detRep (Fin 1) (cj γ (ω a) * absPow k (((n : ℂ) - 1) / 2))) F := by
  let κ := (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ).toLinearEquiv
  refine smInd_conj (j := (κ.toAddEquiv.trans γ.toAddEquiv).trans κ.symm.toAddEquiv) ⟨fun z v => ?_, fun p v => ?_⟩
  · show κ.symm (γ (κ (z • v))) = γ z • κ.symm (γ (κ v))
    rw [map_smul, smul_eq_mul, map_mul, ← map_smul, smul_eq_mul]
  · apply κ.injective
    show κ (κ.symm (γ (κ ((deltaHalf k _ (leviProj k e p) : ℂ) • piTensor _ (leviProj k e p) v)))) =
      κ ((deltaHalf k _ (leviProj k e p) : ℂ) • piTensor _ (leviProj k e p) (κ.symm (γ (κ v))))
    generalize leviProj k e p = l
    have h1 := fun χ t => GlobalTheory.PermPrin.constEquiv_piTensor_detRep (k := k) (n := n) χ l t
    have h2 : ∀ t, PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ t = κ t := fun _ => rfl
    simp only [h2] at h1
    rw [κ.apply_symm_apply, κ.map_smul, κ.map_smul, h1, h1, κ.apply_symm_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_assoc, map_mul, deltaHalf_apply, Units.coe_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      map_prod]
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    have h3 : ((modExp (fun _ : Fin n => Fin 1) a : ℤ) : ℂ) / 2 + ((n : ℂ) - 1) / 2 = ((n - 1 - a : ℕ) : ℂ) := by
      rw [modExp_fin _ (fun _ => by simp), Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    have h4 : ∀ (x : kˣ) (c : ℂ), (absPow k (((modExp (fun _ : Fin n => Fin 1) a : ℤ) : ℂ) / 2) x : ℂ) *
        (c * absPow k (((n : ℂ) - 1) / 2) x) = c * absPow k ((n - 1 - a : ℕ) : ℂ) x := fun x c => by
      rw [← h3, absPow_add, MonoidHom.mul_apply, Units.val_mul]
      ring
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, h4, h4, map_mul, cj_abs, cj_val]

end Loc

section Loc2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem exists_order (ω : Fin n → kˣ →* ℂˣ) :
    ∃ p : Equiv.Perm (Fin n), ∀ i j, i < j → ω (p j) ≠ ω (p i) * absPow k 1 := by
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  let t : Fin n → ℝ := fun i => ‖(ω i ϖ : ℂ)‖
  refine ⟨Tuple.sort t, fun i j hij e => ?_⟩
  have h1 : t (Tuple.sort t i) ≤ t (Tuple.sort t j) := Tuple.monotone_sort t hij.le
  have h2 : nabs k ϖ < 1 := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ, zpow_neg, zpow_one]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[k]))
  have h3 : t (Tuple.sort t j) = t (Tuple.sort t i) * nabs k ϖ := by
    simp only [t]
    rw [e, MonoidHom.mul_apply, Units.val_mul, norm_mul, val_absPow, Complex.cpow_one, Complex.norm_real,
      Real.norm_of_nonneg (nabs_pos' k ϖ).le]
  have h4 : 0 < t (Tuple.sort t i) := norm_pos_iff.2 (Units.ne_zero _)
  nlinarith

private theorem lfactors (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (ho : ∀ i j, i < j → ω j ≠ ω i * absPow k 1) : ∃ 𝔪, LFactors 𝔪 fun a => IrrGL.ofChar (ω a) (hω a) := by
  refine ⟨_, fun a => .single _ (IrrGL.isCusp_ofChar (ω a) (hω a)), ⟨rfl, fun i j hij hp => ho i j hij ?_⟩,
    fun a => (single_spec _).2.1⟩
  obtain ⟨m, h1, h2, -, e⟩ := Segment.precedes_iff.1 hp
  obtain rfl : m = 1 := le_antisymm h2 h1
  simp only [Segment.single, Segment.first_ofFirst, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
  simpa using e

private theorem order_cj (γ : ℂ ≃+* ℂ) {χ ψ : kˣ →* ℂˣ} (h : cj γ χ = cj γ ψ * absPow k 1) : χ = ψ * absPow k 1 := by
  refine MonoidHom.ext fun x => Units.ext (γ.injective ?_)
  have h1 := cj_abs γ 1 x
  rw [Nat.cast_one] at h1
  rw [← cj_val, h, MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, map_mul, h1, cj_val]

private theorem sum_deg (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) :
    ∑ a, (IrrGL.ofChar (ω a) (hω a)).1 = n := by simp [IrrGL.ofChar]

private theorem twist_prod (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) (hd : ∑ _ : Fin n, 1 = n)
    {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    Nonempty ((twist (prodIrr _ (sum_deg ω hω)) (detChar (Fin n) η)).Equiv
      (multiProd (stdBlocks (fun _ => 1) hd) fun a => detRep (Fin 1) (ω a * η))) :=
  ⟨(multiProdTwistEquiv _ _ hη).trans (multiProdEquiv _ fun a =>
    (twistEquiv (equivRep (IrrRep.det (Fin 1) (ω a) (hω a))).symm _).trans (.mk (.refl ℂ ℂ) fun g => by
      refine LinearMap.ext fun x : ℂ => ?_
      show (η _ : ℂ) • ofChar (detChar (Fin 1) (ω a)) g x = ofChar (detChar (Fin 1) (ω a * η)) g x
      rw [ofChar_apply, ofChar_apply, detChar_apply, detChar_apply, MonoidHom.mul_apply, Units.val_mul, smul_eq_mul]
      exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm))⟩

private theorem good_cosocle (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) (π : IrrRep (GL (Fin n) k))
    (hπ : IsCosocle π.ρ (prodIrr _ (sum_deg ω hω))) : UpperTheory.Zero.LLC.Good (cls π) := by
  have hc : ∀ a, HasSupport (IrrGL.ofChar (ω a) (hω a)).rep {IrrGL.ofChar (ω a) (hω a)} := fun a =>
    hasSupport_self (IrrGL.isCusp_ofChar (ω a) (hω a))
  have h1 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hc π.irr hπ.isSubquotient
  refine ⟨_, h1.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr), fun y hy => Or.inl ?_⟩
  obtain ⟨a, -, hy⟩ := Multiset.mem_sum.1 hy
  rw [Multiset.mem_singleton.1 hy]
  rfl

private theorem cosocle_main (γ : ℂ ≃+* ℂ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {σ : Representation ℂ (GL (Fin n) k) V} {σ' : Representation ℂ (GL (Fin n) k) V'} {f : V ≃+ V'}
    (hf : Cj γ σ σ' f) (hi : σ'.IsIrreducible) (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) {s : ℂ}
    (hs : ((n : ℂ) - 1) / 2 + s = 0)
    (h : IsCosocle (twist σ (detChar (Fin n) (absPow k s))) (prodIrr _ (sum_deg ω hω))) :
    IsCosocle (twist σ' (detChar (Fin n) (absPow k s)))
      (prodIrr _ (sum_deg (fun a => cj γ (ω a)) fun a => cj_smooth γ (hω a))) := by
  have hd : ∑ _ : Fin n, 1 = n := by simp
  have e1 : detChar (Fin n) (absPow k (((n : ℂ) - 1) / 2)) * detChar (Fin n) (absPow k s) = 1 :=
    MonoidHom.ext fun g => by
      rw [MonoidHom.mul_apply, detChar_apply, detChar_apply, ← MonoidHom.mul_apply, ← absPow_add, hs, absPow_zero]
      rfl
  have h1 := cosocle_move h e1
  have E := Classical.choice (twist_prod ω hω hd (isSmoothChar_absPow (((n : ℂ) - 1) / 2)))
  have E' := Classical.choice (twist_prod (fun a => cj γ (ω a)) (fun a => cj_smooth γ (hω a)) hd
    (isSmoothChar_absPow (((n : ℂ) - 1) / 2)))
  refine (prod_conj γ (stdBlocks (fun _ => 1) hd) ω).elim fun F hF => ?_
  have h3 := h1.of_equiv (.refl σ) E
  have h2 := cosocle_conj hF hf hi h3
  have h4 := h2.of_equiv (.refl σ') E'.symm
  exact cosocle_move' h4 e1

end Loc2

section Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {n : ℕ}

private theorem exists_basis {Γ : Type} (f : Γ → Module.End ℂ (Fin n → ℂ)) (hs : ∀ g, (f g).IsSemisimple)
    (hc : ∀ g k, Commute (f g) (f k)) :
    ∃ B : Module.Basis (Fin n) ℂ (Fin n → ℂ), ∀ j g, ∃ c : ℂ, f g (B j) = c • B j := by
  have h1 := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun g k _ => hc g k) fun g => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun g => (hs g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
  let T : Set (Fin n → ℂ) := {v | ∀ g, ∃ c : ℂ, f g v = c • v}
  have h2 : ⊤ ≤ Submodule.span ℂ T := by
    rw [← h1]
    exact iSup_le fun χ v hv => Submodule.subset_span fun g =>
      ⟨χ g, Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv g)⟩
  let B := Module.Basis.ofSpan h2
  have h3 := Module.Basis.ofSpan_subset h2
  refine ⟨B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin n))), fun j => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact h3 ⟨_, rfl⟩

private theorem exists_chars (b : WDRep h (Fin n → ℂ)) (χ : Fin n → Dec (F := E) A →* ℂˣ)
    (hb : ∀ s : ↥(Ine (F := E) A), b.ρ (ineIncl h s) =
      Matrix.toLin' (Matrix.diagonal fun i => (χ i (Subgroup.inclusion (Ine_le_Dec A) s) : ℂ))) :
    ∃ (B : Module.Basis (Fin n) ℂ (Fin n → ℂ)) (ξ : Fin n → Weil h →* ℂˣ), (∀ j, GlobalTheory.WeilDeligne.IsSmooth (ξ j)) ∧
      ∀ j g, b.ρ g (B j) = (ξ j g : ℂ) • B j := by
  have hc : ∀ g k, Commute (b.ρ g) (b.ρ k) := fun g k => by
    have h0 : deg ((k * g)⁻¹ * (g * k)) = 0 := by simp [add_comm]; ring
    have h1 : b.ρ ((k * g)⁻¹ * (g * k)) = 1 := by
      refine (hb ⟨_, deg_eq_zero_iff.1 h0⟩).trans ?_
      have h3 : ∀ i, χ i (Subgroup.inclusion (Ine_le_Dec A) ⟨_, deg_eq_zero_iff.1 h0⟩) = 1 := fun i => by
        let c := (χ i).comp (Subgroup.inclusion (Weil_le_Dec h))
        show c ((k * g)⁻¹ * (g * k)) = 1
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (c g), inv_mul_cancel]
      simp only [h3, Units.val_one, Matrix.diagonal_one, Matrix.toLin'_one]
      rfl
    show _ = _
    rw [← map_mul, ← map_mul, ← mul_inv_cancel_left (k * g) (g * k), map_mul, h1, mul_one]
  obtain ⟨B, hB⟩ := exists_basis b.ρ b.semisimple hc
  choose c hc using hB
  have inj : ∀ j (x y : ℂ), x • B j = y • B j → x = y := fun j x y e => smul_left_injective ℂ (B.ne_zero j) e
  let d : Fin n → Weil h →* ℂ := fun j =>
    { toFun := c j
      map_one' := inj j _ _ (by rw [← hc]; simp)
      map_mul' := fun g k => inj j _ _ (by
        rw [← hc, map_mul, Module.End.mul_apply, hc, map_smul, hc, smul_smul, mul_comm]) }
  refine ⟨B, fun j => (d j).toHomUnits, fun j => b.smooth.of_le fun g hg => Units.ext (inj j _ _ ?_), hc⟩
  show c j g • B j = _
  rw [← hc, hg]
  simp

private theorem equivFun_ρ (b : WDRep h (Fin n → ℂ)) (B : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (ξ : Fin n → Weil h →* ℂˣ) (hB : ∀ j g, b.ρ g (B j) = (ξ j g : ℂ) • B j) (g : Weil h) (v : Fin n → ℂ) :
    B.equivFun (b.ρ g v) = diagEnd (fun j => (ξ j g : ℂ)) (B.equivFun v) := by
  have : B.equivFun.toLinearMap ∘ₗ b.ρ g = diagEnd (fun j => (ξ j g : ℂ)) ∘ₗ B.equivFun.toLinearMap :=
    B.ext fun j => funext fun i => by
      simp only [LinearMap.comp_apply, hB, map_smul, diagEnd_apply, LinearEquiv.coe_coe, Pi.smul_apply,
        Module.Basis.equivFun_self, smul_eq_mul]
      split_ifs with e
      · rw [e]
      · simp
  exact LinearMap.congr_fun this v

private theorem sumList_chars : ∀ (n : ℕ) (ξ : Fin n → Weil h →* ℂˣ) (hξ : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (ξ j)),
    sumList (List.ofFn fun i => WD.lpOfChar h (ξ i) (hξ i)) = WD.mk (WDRep.ofChars h ξ hξ)
  | 0, ξ, hξ => by
    rw [List.ofFn_zero]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | n + 1, ξ, hξ => by
    rw [List.ofFn_succ, SatakeLaw.sumList_cons, sumList_chars n (fun i => ξ i.succ), WD.lpOfChar, WD.lpSum_mk]
    refine WD.sound ⟨SatakeLaw.consEquiv n, fun σ v => funext fun i => ?_, fun v => funext fun i => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [SatakeLaw.consEquiv]
    · refine Fin.cases ?_ (fun j => ?_) i <;> simp [SatakeLaw.consEquiv]

private theorem rc_cosocle {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc)
    (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (ho : ∀ i j, i < j → ω j ≠ ω i * absPow _ 1) (π : IrrRep (GL (Fin n) (w.adicCompletion E)))
    (hπ : IsCosocle π.ρ (prodIrr _ (sum_deg ω hω))) :
    rc (cls π) = WD.mk (WDRep.ofChars h (fun i => (ω i).comp a) fun i => ha.smooth (hω i)) := by
  obtain ⟨𝔪, h𝔪⟩ := lfactors ω hω ho
  rw [hrc.langlandsQuotient h𝔪 _ hπ, ← sumList_chars]
  simp only [H.one]

private theorem type_conj (γ : ℂ ≃+* ℂ) (b : WDRep h (Fin n → ℂ)) (B : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (ξ : Fin n → Weil h →* ℂˣ) (hB : ∀ j g, b.ρ g (B j) = (ξ j g : ℂ) • B j) (χ : Fin n → Ine (F := E) A →* ℂˣ)
    (hb : ∀ s : ↥(Ine (F := E) A), b.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (χ i s : ℂ)))
    (hξ : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (cj γ (ξ j))) :
    IsTypeWD h (fun i => W.pushCh γ.toRingHom (χ i)) (WD.mk (WDRep.ofChars h (fun j => cj γ (ξ j)) hξ)) := by
  let e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun v i => γ (B.equivFun.symm (fun j => γ.symm (v j)) i)
      invFun := fun v i => γ (B.equivFun (fun j => γ.symm (v j)) i)
      map_add' := fun u v => funext fun i => by
        have : (fun j => γ.symm ((u + v) j)) = (fun j => γ.symm (u j)) + fun j => γ.symm (v j) :=
          funext fun j => map_add _ _ _
        rw [this, LinearEquiv.map_add]
        exact map_add γ _ _
      map_smul' := fun c v => funext fun i => by
        have : (fun j => γ.symm ((c • v) j)) = γ.symm c • fun j => γ.symm (v j) := funext fun j => map_mul _ _ _
        rw [this, LinearEquiv.map_smul]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, RingHom.id_apply]
      left_inv := fun v => funext fun i => by
        simp only [RingEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      right_inv := fun v => funext fun i => by
        simp only [RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] }
  obtain ⟨h1, h2⟩ : (∀ σ v, e ((WDRep.ofChars h (fun j => cj γ (ξ j)) hξ).ρ σ v) =
      ((WDRep.ofChars h (fun j => cj γ (ξ j)) hξ).transport e).ρ σ (e v)) ∧
      ((WDRep.ofChars h (fun j => cj γ (ξ j)) hξ).transport e).N = 0 :=
    ⟨fun σ v => by
      show _ = e.conjAlgEquiv ℂ _ (e v)
      simp, map_zero (e.conjAlgEquiv ℂ)⟩
  refine ⟨_, (WD.sound (WDRep.iso_transport _ e)).symm, h2, fun s => LinearMap.ext fun v => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective v
  rw [← h1]
  funext i
  have h3 := equivFun_ρ b B ξ hB (ineIncl h s) (B.equivFun.symm fun j => γ.symm (v j))
  rw [LinearEquiv.apply_symm_apply, hb, ← LinearEquiv.eq_symm_apply] at h3
  have h4 : (fun j => γ.symm ((WDRep.ofChars h (fun j => cj γ (ξ j)) hξ).ρ (ineIncl h s) v j)) =
      diagEnd (fun j => (ξ j (ineIncl h s) : ℂ)) fun j => γ.symm (v j) := funext fun j => by
    rw [WDRep.ofChars_ρ, diagEnd_apply, diagEnd_apply, map_mul, cj_val, γ.symm_apply_apply]
  show γ (B.equivFun.symm (fun j => γ.symm ((WDRep.ofChars h (fun j => cj γ (ξ j)) hξ).ρ (ineIncl h s) v j)) i) = _
  rw [h4, ← h3, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal, map_mul]
  rfl

end Gal

end UpperTheory.V.Z.Win.T2.TypeConj

open UpperTheory.V.Z.Win.T2.TypeConj in
theorem UpperTheory.V.Z.Win.T2.typeConj :
    type_of% @UpperTheory.V.Hi.typeConj := by
  intro P L Ω _ _ _ _ _ n w A h rc hrc γ σ σ' f hf1 hf2 χ _ ⟨b, hb, hN, hρ⟩
  obtain ⟨a, ha, ε, H⟩ := UpperTheory.V.Z.Win.toV hrc
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  obtain ⟨B₀, ξ, hξ, hB₀⟩ := exists_chars b χ hρ
  choose ω₀ hω₀ e using fun j => ha.factor (ξ j) (hξ j)
  obtain ⟨p, ho⟩ := exists_order ω₀
  let ω := fun j => ω₀ (p j)
  have hω : ∀ j, IsSmoothChar (ω j) := fun j => hω₀ _
  let B := B₀.reindex p.symm
  have hB : ∀ j g, b.ρ g (B j) = ((ω j).comp a g : ℂ) • B j := fun j g => by
    simp only [B, ω, Module.Basis.reindex_apply, Equiv.symm_symm, hB₀, e]
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  let tw : SmIrr (GLw n w) → IrrRep (GL (Fin n) (w.adicCompletion L)) := fun τ =>
    ⟨_, twist τ.ρ (detChar (Fin n) (absPow _ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))),
      isSmooth_twist τ.smooth (isSmoothChar_absPow _).detChar, isIrreducible_twist τ.irred _⟩
  have htw : ∀ τ, algNorm τ = cls (tw τ) := fun τ => IrrGL.tw_of _ _ _ _ (isSmoothChar_absPow _)
  obtain ⟨𝔪, h𝔪⟩ := lfactors ω hω ho
  obtain ⟨π, hπ⟩ := P.loc.cos _ 𝔪 n n _ (sum_deg ω hω) h𝔪
  have h1 : rc (cls π) = rc (cls (tw σ)) := by
    rw [rc_cosocle hrc H ω hω ho π hπ, ← htw, ← hb]
    exact (WD.sound ⟨B.equivFun, equivFun_ρ b B _ hB, fun v => by simp [hN]⟩).symm
  have hG : UpperTheory.Zero.LLC.Good (cls π) := good_cosocle ω hω π hπ
  obtain ⟨φ⟩ := (IrrGL.of_eq_of (π := π.ρ) (σ := (tw σ).ρ) (hs := π.smooth) (hi := π.irr) (hs' := (tw σ).smooth)
    (hi' := (tw σ).irr)).1 (H.inj _ _ hG h1.symm).symm
  have h2 := cosocle_main γ ⟨hf1, hf2⟩ σ'.irred ω hω e0 (hπ.of_equiv φ (.refl _))
  rw [htw, rc_cosocle hrc H _ _ (fun i j hij e => ho i j hij (order_cj γ e)) (tw σ') h2]
  exact type_conj γ b B _ hB _ hρ _
