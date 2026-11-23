import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.IdealNormClassCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTransport

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.desc :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal], e ≠ 0 → Procyc L Ω l → cycU l U = cycU l (galOf k L Ω) →
        ∃ Φ : Sha D e ≃ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e, IsDesc L D e U Φ.toLinearMap := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e U _ he hpro hcyc
  have hfam := galEmbFam k L Ω l
  have hcycE : ∀ h : G L Ω, cycZ k Ω l (galEmb k L Ω h) = cycZ L Ω l h := fun h => by
    rw [← MonoidHom.comp_apply, hfam.2.2.1]
  have hlift : ∀ σ ∈ galOf k L Ω, ∃ h : G L Ω, galEmb k L Ω h = σ := by
    intro σ hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, by ext x; rfl⟩
  have hmap : Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) = cycU l U := by
    rw [hcyc]
    ext σ
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · intro x
        exact g.commutes x
      · rw [MonoidHom.mem_ker, hcycE]
        exact (Subgroup.mem_inf.1 hg).2
    · intro hσ
      obtain ⟨hσG, hσK⟩ := Subgroup.mem_inf.1 hσ
      obtain ⟨h, rfl⟩ := hlift σ hσG
      refine ⟨h, Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker, ← hcycE]
      exact hσK
  obtain ⟨Ψ, hΨ⟩ := dinfTransport k Ω L Ω (algebraMap k L) (RingEquiv.refl Ω)
    (fun x => IsScalarTower.algebraMap_apply k L Ω x) (galEmb k L Ω) (fun g x => rfl)
    l l U ⊤ hmap
  have hdTw : ∀ (g : G k Ω) (χ : Dinf l l U) (w : cycU l U),
      ((dTw l l U e g χ : Dinf l l U) : cycU l U → QZ l) w =
        (((cycZ k Ω l ^ (-e)) g : ℤ_[l]ˣ) : ℤ_[l]) • (χ : cycU l U → QZ l) (conjHom (cycU l U) g w) := by
    intro g χ w
    rfl
  have hq : ∀ (h : G L Ω) (m : QZ l),
      qzG L Ω l e h m = (((cycZ L Ω l ^ (-e)) h : ℤ_[l]ˣ) : ℤ_[l]) • m := fun h m => rfl
  have hqE : ∀ (h : G L Ω) (m : QZ l),
      (((cycZ k Ω l ^ (-e)) (galEmb k L Ω h) : ℤ_[l]ˣ) : ℤ_[l]) • m = qzG L Ω l e h m := by
    intro h m
    rw [← hfam.2.2.2 e]
    rfl
  have hmemE : ∀ u : cycU l (⊤ : Subgroup (G L Ω)), galEmb k L Ω u ∈ cycU l U := fun u =>
    hmap ▸ Subgroup.mem_map_of_mem _ u.2
  let E : cycU l (⊤ : Subgroup (G L Ω)) → cycU l U := fun u => ⟨galEmb k L Ω u, hmemE u⟩
  have hEsurj : ∀ w : cycU l U, ∃ u, E u = w := by
    intro w
    have hw : (w : G k Ω) ∈ Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) := by
      rw [hmap]
      exact w.2
    obtain ⟨u, hu, huw⟩ := hw
    exact ⟨⟨u, hu⟩, Subtype.ext huw⟩
  have key : ∀ χ : Dinf l l U, χ ∈ ShaD l l U (galOf k L Ω) e ↔
      ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro χ
    have hX : ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        XDual l (Uinf L Ω l) ℤ_[l] (QZ l) := (Ψ χ).2
    have hΨE : ∀ u, ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) :
        cycU l (⊤ : Subgroup (G L Ω)) → QZ l) u = (χ : cycU l U → QZ l) (E u) :=
      fun u => hΨ χ u (E u) rfl
    constructor
    · intro hinv
      refine Submodule.mem_inf.2 ⟨hX, (Submodule.mem_iInf _).2 fun h => ?_⟩
      intro u u' huu
      rw [hΨE, hΨE]
      have hg : galEmb k L Ω h ∈ galOf k L Ω := fun x => h.commutes x
      have hinvg := (Representation.mem_invariants _ _).1 hinv ⟨_, hg⟩
      have h2 : ((dTw l l U e (galEmb k L Ω h) χ : Dinf l l U) : cycU l U → QZ l) (E u') =
          (χ : cycU l U → QZ l) (E u') :=
        congrArg (fun y : Dinf l l U => (y : cycU l U → QZ l) (E u')) hinvg
      rw [hdTw] at h2
      have hconj : conjHom (cycU l U) (galEmb k L Ω h) (E u') = E u := by
        apply Subtype.ext
        show (galEmb k L Ω h)⁻¹ * galEmb k L Ω u' * galEmb k L Ω h = galEmb k L Ω u
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        ext x
        show h⁻¹ ((u' : G L Ω) (h x)) = (u : G L Ω) x
        rw [show (u' : G L Ω) (h x) = h ((u : G L Ω) x) from huu x, AlgEquiv.aut_inv,
          AlgEquiv.symm_apply_apply]
      rw [hconj, hqE] at h2
      exact h2.symm
    · intro hE
      obtain ⟨_, hC⟩ := Submodule.mem_inf.1 hE
      rw [Submodule.mem_iInf] at hC
      refine (Representation.mem_invariants _ _).2 fun g => ?_
      obtain ⟨h, hh⟩ := hlift g g.2
      apply Subtype.ext
      funext w
      show ((dTw l l U e (g : G k Ω) χ : Dinf l l U) : cycU l U → QZ l) w = (χ : cycU l U → QZ l) w
      rw [hdTw]
      obtain ⟨u', rfl⟩ := hEsurj w
      have hu : h⁻¹ * (u' : G L Ω) * h ∈ cycU l (⊤ : Subgroup (G L Ω)) := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
          MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 u'.2).2, mul_one, inv_mul_cancel]
      have hcond := hC h ⟨_, hu⟩ u' (fun x => by
        show (u' : G L Ω) (h x) = h ((h⁻¹ * (u' : G L Ω) * h) x)
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      rw [hΨE, hΨE] at hcond
      have hconj : conjHom (cycU l U) (g : G k Ω) (E u') = E ⟨_, hu⟩ := by
        apply Subtype.ext
        show (g : G k Ω)⁻¹ * galEmb k L Ω u' * (g : G k Ω) = galEmb k L Ω (h⁻¹ * (u' : G L Ω) * h)
        rw [← hh, map_mul, map_mul, map_inv]
      rw [hconj, ← hh, hqE]
      exact hcond.symm
  have hR : ∀ x : Sha D e, resInf D e (x : H1 (qzTw D e)) ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro x
    rw [← resInfOnto L Ω l D e he hpro]
    exact Submodule.mem_map_of_mem x.2
  have hED : ∀ f, f ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) → f ∈ Dinf l l (⊤ : Subgroup (G L Ω)) :=
    fun f hf => (Submodule.mem_inf.1 hf).1
  let R0 : Sha D e →ₗ[ℤ_[l]] Dinf l l (⊤ : Subgroup (G L Ω)) :=
    LinearMap.codRestrict _ ((resInf D e).comp (Sha D e).subtype) (fun x => hED _ (hR x))
  let f : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e :=
    LinearMap.codRestrict _ (Ψ.symm.toLinearMap.comp R0) (fun x => (key _).2 (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hR x))
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : Ψ.symm (R0 x) = Ψ.symm (R0 y) := congrArg Subtype.val hxy
    have h2 : R0 x = R0 y := Ψ.symm.injective h1
    have h3 : resInf D e x = resInf D e y := congrArg Subtype.val h2
    exact Subtype.ext (resInfInj L Ω l D e he hpro h3)
  have hfsurj : Function.Surjective f := by
    intro χ
    have hm := (key (χ : Dinf l l U)).1 χ.2
    rw [← resInfOnto L Ω l D e he hpro] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    show Ψ.symm (R0 ⟨x, hx⟩) = χ
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hxe
  refine ⟨LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩, ?_⟩
  intro x u u' hu
  show ((Ψ.symm (R0 x) : Dinf l l U) : cycU l U → QZ l) u' = resInf D e x u
  rw [← hΨ (Ψ.symm (R0 x)) u u' hu, LinearEquiv.apply_symm_apply]
  rfl
