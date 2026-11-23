import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.PullbackAffine
import GroundTheory.ArithmeticGeometry.EtaleCompletion.QcohZariski
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {W T U : Scheme.{u}}

lemma pullbackUnitApp_smul_at (g : T ⟶ U) (N : U.Modules) (O : U.Opens) (a : Γ(U, O))
    (n : Γ(N, O)) :
    Etale.pullbackUnitApp g N O (a • n) = g.app O a • Etale.pullbackUnitApp g N O n :=
  Scheme.Modules.Hom.app_smul _ a n

def sectionLinearAt {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') (O : X.Opens) :
    Γ(P, O) →ₗ[Γ(X, O)] Γ(P', O) where
  toFun := θ.app O
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul θ

@[simp] lemma sectionLinearAt_apply {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P')
    (O : X.Opens) (x : Γ(P, O)) : sectionLinearAt θ O x = θ.app O x := rfl

def IsBaseChangeAt (g : T ⟶ U) (N : U.Modules) (O : U.Opens) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(T, g ⁻¹ᵁ O) Q] (ψ : Γ(N, O) →+ Q),
    (∀ (a : Γ(U, O)) (n : Γ(N, O)), ψ (a • n) = g.app O a • ψ n) →
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) →ₗ[Γ(T, g ⁻¹ᵁ O)] Q,
      ∀ n, ψ' (Etale.pullbackUnitApp g N O n) = ψ n

lemma IsBaseChangeAt.comp {f : W ⟶ T} {g : T ⟶ U} {N : U.Modules} {O : U.Opens}
    (hg : IsBaseChangeAt g N O)
    (hf : IsBaseChangeAt f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ O)) :
    IsBaseChangeAt (f ≫ g) N O := by
  intro Q _ instQ ψ hψ
  letI instW : Module Γ(W, f ⁻¹ᵁ (g ⁻¹ᵁ O)) Q := instQ
  letI : Module Γ(T, g ⁻¹ᵁ O) Q := Module.compHom Q (f.app (g ⁻¹ᵁ O)).hom
  have hsm : ∀ (t : Γ(T, g ⁻¹ᵁ O)) (q : Q), t • q = f.app (g ⁻¹ᵁ O) t • q := fun _ _ => rfl
  obtain ⟨ψ₁, hψ₁, u₁⟩ := hg Q ψ (fun a n => by
    rw [hψ, hsm]
    change (f ≫ g).app O a • ψ n = (f.app (g ⁻¹ᵁ O)) ((g.app O) a) • ψ n
    rw [Scheme.Hom.comp_app]
    rfl)
  obtain ⟨ψ₂, hψ₂, u₂⟩ := hf Q ψ₁.toAddMonoidHom (fun t x => ψ₁.map_smul t x)
  let c := (Scheme.Modules.pullbackComp f g).app N
  let O' := (f ≫ g) ⁻¹ᵁ O
  have hc : ∀ n, c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n) =
      Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n) :=
    Etale.pullbackUnitApp_comp f g N O
  have hchi : ∀ x, c.hom.app O' (c.inv.app O' x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]; rfl
  let Φ : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, O') →ₗ[Γ(W, O')] Q :=
    { toFun := fun x => ψ₂ (c.inv.app O' x)
      map_add' := fun x y => by
        change ψ₂ (c.inv.app O' (x + y)) = ψ₂ (c.inv.app O' x) + ψ₂ (c.inv.app O' y)
        erw [map_add, map_add]
      map_smul' := fun w x => by
        change ψ₂ (c.inv.app O' (w • x)) = w • ψ₂ (c.inv.app O' x)
        erw [Scheme.Modules.Hom.app_smul]
        exact ψ₂.map_smul w _ }
  refine ⟨Φ, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · change ψ₂ (c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n)) = ψ n
    rw [hc, hψ₂]
    exact hψ₁ n
  · let χ : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N),
        f ⁻¹ᵁ (g ⁻¹ᵁ O)) →ₗ[Γ(W, f ⁻¹ᵁ (g ⁻¹ᵁ O))] Q :=
      { toFun := fun y => ψ'' (c.hom.app O' y)
        map_add' := fun x y => by
          change ψ'' (c.hom.app O' (x + y)) = ψ'' (c.hom.app O' x) + ψ'' (c.hom.app O' y)
          erw [map_add, map_add]
        map_smul' := fun w y => by
          change ψ'' (c.hom.app O' (w • y)) = w • ψ'' (c.hom.app O' y)
          erw [Scheme.Modules.Hom.app_smul]
          exact ψ''.map_smul w _ }
    have hχ : ∀ n, χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n)) =
        ψ n := fun n => by
      change ψ'' (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O)
        (Etale.pullbackUnitApp g N O n))) = ψ n
      rw [← hc, hchi]
      exact hψ'' n
    let χ₁ : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) →ₗ[Γ(T, g ⁻¹ᵁ O)] Q :=
      { toFun := fun x => χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x)
        map_add' := fun x y => by
          change χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (x + y)) = _
          erw [map_add, map_add]
        map_smul' := fun t x => by
          change χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (t • x)) =
            t • χ (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x)
          rw [pullbackUnitApp_smul_at, map_smul, hsm] }
    have h₁ : χ₁ = ψ₁ := u₁ χ₁ hχ
    have h₂ : χ = ψ₂ := u₂ χ (fun x => congrArg (fun l => l x) h₁)
    ext x
    change ψ'' x = ψ₂ (c.inv.app O' x)
    rw [← h₂]
    change ψ'' x = ψ'' (c.hom.app O' (c.inv.app O' x))
    rw [hchi]

lemma isBaseChangeAt_of_isOpenImmersion (j : T ⟶ U) [IsOpenImmersion j] (N : U.Modules)
    {O : U.Opens} (hO : O ≤ j.opensRange) : IsBaseChangeAt j N O := by
  intro Q _ _ ψ hψ
  have hb := Etale.pullbackUnitApp_bijective j N hO
  have : IsIso (j.app O) := Scheme.Hom.isIso_app j O hO
  let e := AddEquiv.ofBijective (Etale.pullbackUnitApp j N O) hb
  have he : ∀ n, e.symm (Etale.pullbackUnitApp j N O n) = n := fun n => e.symm_apply_apply n
  have hs : ∀ x, Etale.pullbackUnitApp j N O (e.symm x) = x := fun x => e.apply_symm_apply x
  refine ⟨{ toFun := fun x => ψ (e.symm x)
            map_add' := fun x y => by simp
            map_smul' := fun t x => ?_ }, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Γ(U, O), j.app O a = t :=
      ⟨(asIso (j.app O)).inv t, by simp⟩
    simp only [RingHom.id_apply]
    rw [← hψ, ← hs x, he, ← pullbackUnitApp_smul_at, he]
  · simp [he]
  · ext x
    obtain ⟨n, rfl⟩ := hb.2 x
    simp [he, hψ'']

lemma IsBaseChangeAt.of_comp_isOpenImmersion {f : W ⟶ T} [IsOpenImmersion f] {g : T ⟶ U}
    {N : U.Modules} {O : U.Opens} (hO : g ⁻¹ᵁ O ≤ f.opensRange)
    (h : IsBaseChangeAt (f ≫ g) N O) : IsBaseChangeAt g N O := by
  intro Q _ _ ψ hψ
  have : IsIso (f.app (g ⁻¹ᵁ O)) := Scheme.Hom.isIso_app f _ hO
  let ρ := asIso (f.app (g ⁻¹ᵁ O))
  let O' := (f ≫ g) ⁻¹ᵁ O
  letI instW : Module Γ(W, O') Q := Module.compHom Q ρ.inv.hom
  have hsm : ∀ (w : Γ(W, O')) (q : Q), w • q = ρ.inv w • q := fun _ _ => rfl
  have hρ : ∀ t : Γ(T, g ⁻¹ᵁ O), ρ.inv (f.app (g ⁻¹ᵁ O) t) = t := fun t => by
    rw [← ConcreteCategory.comp_apply]
    change (ρ.hom ≫ ρ.inv) t = t
    rw [ρ.hom_inv_id]
    rfl
  have hρ' : ∀ w : Γ(W, O'), f.app (g ⁻¹ᵁ O) (ρ.inv w) = w := fun w => by
    change (ρ.inv ≫ ρ.hom) w = w
    rw [ρ.inv_hom_id]
    rfl
  obtain ⟨Ψ, hΨ, uΨ⟩ := h Q ψ (fun a n => by
    rw [hψ, hsm]
    change _ = ρ.inv ((f.app (g ⁻¹ᵁ O)) ((g.app O) a)) • ψ n
    rw [hρ])
  have hb := Etale.pullbackUnitApp_bijective f ((Scheme.Modules.pullback g).obj N) hO
  let e := AddEquiv.ofBijective (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O)) hb
  let c := (Scheme.Modules.pullbackComp f g).app N
  have hchi : ∀ x, c.inv.app O' (c.hom.app O' x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.hom_inv_id]; rfl
  have hchi' : ∀ x, c.hom.app O' (c.inv.app O' x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]; rfl
  let ψ' : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) →ₗ[Γ(T, g ⁻¹ᵁ O)] Q :=
    { toFun := fun x => Ψ (c.hom.app O' (e x))
      map_add' := fun x y => by
        change Ψ (c.hom.app O' (e (x + y))) = Ψ (c.hom.app O' (e x)) + Ψ (c.hom.app O' (e y))
        erw [map_add, map_add, map_add]
      map_smul' := fun t x => by
        change Ψ (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (t • x))) =
          t • Ψ (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x))
        rw [pullbackUnitApp_smul_at]
        have h1 := Scheme.Modules.Hom.app_smul c.hom (U := O') (f.app (g ⁻¹ᵁ O) t)
          (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) x)
        erw [h1, map_smul, hsm, hρ] }
  refine ⟨ψ', fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · change Ψ (c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n))) =
      ψ n
    have hcomp := Etale.pullbackUnitApp_comp f g N O n
    have h2 : c.hom.app O' (Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (Etale.pullbackUnitApp g N O n)) =
        Etale.pullbackUnitApp (f ≫ g) N O n :=
      (congrArg (fun z => c.hom.app O' z) hcomp).symm.trans (hchi' _)
    exact (congrArg Ψ h2).trans (hΨ n)
  · let χ : Γ((Scheme.Modules.pullback (f ≫ g)).obj N, O') →ₗ[Γ(W, O')] Q :=
      { toFun := fun x => ψ'' (e.symm (c.inv.app O' x))
        map_add' := fun x y => by
          change ψ'' (e.symm (c.inv.app O' (x + y))) =
            ψ'' (e.symm (c.inv.app O' x)) + ψ'' (e.symm (c.inv.app O' y))
          erw [map_add, map_add, map_add]
        map_smul' := fun w x => by
          change ψ'' (e.symm (c.inv.app O' (w • x))) = ρ.inv w • ψ'' (e.symm (c.inv.app O' x))
          have hs1 : c.inv.app O' (w • x) = w • c.inv.app O' x :=
            Scheme.Modules.Hom.app_smul c.inv w x
          set y : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N),
            f ⁻¹ᵁ (g ⁻¹ᵁ O)) := c.inv.app O' x
          have hs2 : e.symm (c.inv.app O' (w • x)) = ρ.inv w • e.symm y := by
            apply e.injective
            refine (e.apply_symm_apply _).trans ?_
            change c.inv.app O' (w • x) =
              Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O) (ρ.inv w • e.symm y)
            rw [pullbackUnitApp_smul_at, hρ', hs1]
            exact congrArg (fun z => w • z) (e.apply_symm_apply y).symm
          rw [hs2, map_smul] }
    have hχ : χ = Ψ := uΨ χ (fun n => by
      change ψ'' (e.symm (c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n))) = ψ n
      have hcomp := Etale.pullbackUnitApp_comp f g N O n
      have h3 : e.symm (c.inv.app O' (Etale.pullbackUnitApp (f ≫ g) N O n)) =
          Etale.pullbackUnitApp g N O n :=
        (congrArg (fun z => e.symm z) hcomp).trans (e.symm_apply_apply _)
      exact (congrArg ψ'' h3).trans (hψ'' n))
    ext x
    change ψ'' x = Ψ (c.hom.app O' (e x))
    rw [← hχ]
    change ψ'' x = ψ'' (e.symm (c.inv.app O' (c.hom.app O' (e x))))
    have h4 : e.symm (c.inv.app O' (c.hom.app O' (e x))) = x :=
      (congrArg (fun z => e.symm z) (hchi (e x))).trans (e.symm_apply_apply x)
    exact (congrArg ψ'' h4).symm

lemma isBaseChangeAt_top_of_isAffine (h : T ⟶ U) [IsAffine T] [IsAffine U] (N : U.Modules)
    [N.IsQuasicoherent] : IsBaseChangeAt h N ⊤ := by
  intro Q _ instQ ψ hψ
  exact @Etale.existsUnique_pullbackSection T U h _ _ N _ Q _ instQ ψ hψ

theorem isBaseChangeAt_of_isAffineOpen (g : T ⟶ U) (N : U.Modules) [N.IsQuasicoherent]
    {V : U.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen (g ⁻¹ᵁ V)) :
    IsBaseChangeAt g N V := by
  refine IsBaseChangeAt.of_comp_isOpenImmersion (f := (g ⁻¹ᵁ V).ι) (by simp) ?_
  rw [← morphismRestrict_ι g V]
  refine IsBaseChangeAt.comp (isBaseChangeAt_of_isOpenImmersion V.ι N (by simp)) ?_
  rw [Scheme.Opens.ι_preimage_self]
  have : IsAffine V := hV
  have : IsAffine (g ⁻¹ᵁ V) := hV'
  have : ((Scheme.Modules.pullback V.ι).obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N) inferInstance
  exact isBaseChangeAt_top_of_isAffine (g ∣_ V) _

lemma IsBaseChangeAt.span_range {g : T ⟶ U} {N : U.Modules} {O : U.Opens}
    (h : IsBaseChangeAt g N O) :
    Submodule.span Γ(T, g ⁻¹ᵁ O) (Set.range (Etale.pullbackUnitApp g N O)) = ⊤ := by
  set L := Submodule.span Γ(T, g ⁻¹ᵁ O) (Set.range (Etale.pullbackUnitApp g N O))
  obtain ⟨ψ', -, huniq⟩ := h (Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ O) ⧸ L) 0
    (fun a n => by simp)
  have h0 : (0 : _ →ₗ[Γ(T, g ⁻¹ᵁ O)] (_ ⧸ L)) = ψ' := huniq 0 (fun n => by simp)
  have h1 : L.mkQ = ψ' := huniq L.mkQ (fun n => by
    simpa using (Submodule.Quotient.mk_eq_zero L).2 (Submodule.subset_span ⟨n, rfl⟩))
  rw [eq_top_iff]
  intro q _
  have := LinearMap.congr_fun (h1.trans h0.symm) q
  exact (Submodule.Quotient.mk_eq_zero L).1 this

end

end GroundTheory.Arith.SchemeCoh
