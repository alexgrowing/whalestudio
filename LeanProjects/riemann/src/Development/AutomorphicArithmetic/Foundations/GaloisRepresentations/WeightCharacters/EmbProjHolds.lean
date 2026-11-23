import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem proj_of_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G → V →ₗ[ℂ] V)
    (A : Submodule ℂ V) (S : Set (Submodule ℂ V))
    (hSA : ∀ U ∈ S, U ≤ A) (hSs : ∀ U ∈ S, ∀ x, ∀ v ∈ U, ρ x v ∈ U)
    (hSi : ∀ U ∈ S, ∀ N ≤ U, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → N = ⊥ ∨ N = U)
    (hAS : A ≤ sSup S) (ψ : V) (hψA : ψ ∈ A) (hψ : ψ ≠ 0) :
    ∃ U ∈ S, ∃ pr : V →ₗ[ℂ] V, pr ψ ≠ 0 ∧ ∀ f ∈ A, pr f ∈ U ∧ ∀ x, pr (ρ x f) = ρ x (pr f) := by
  classical
  let P : Set (Submodule ℂ V) := {C | C ≤ A ∧ (∀ x, ∀ v ∈ C, ρ x v ∈ C) ∧ ψ ∉ C}
  have hbot : (⊥ : Submodule ℂ V) ∈ P :=
    ⟨bot_le, fun x v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _,
      fun h => hψ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨C, -, hC⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun x v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hz ((hcP hz).2.1 x v hvz)
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcP hz).2.2 hvz) ⊥ hbot
  obtain ⟨hCA, hCs, hψC⟩ := hC.prop
  have hsup : ∀ N ≤ A, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → ¬ N ≤ C → ψ ∈ C ⊔ N := by
    intro N hNA hNs hNC
    by_contra hn
    have hm : C ⊔ N ∈ P := ⟨sup_le hCA hNA, fun x v hv => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (hCs x a ha) (hNs x b hb), hn⟩
    exact hNC (le_sup_right.trans (hC.le_of_ge hm le_sup_left))
  obtain ⟨U, hUS, hUC⟩ : ∃ U ∈ S, ¬ U ≤ C := by
    by_contra hn
    push_neg at hn
    exact hψC (sSup_le hn (hAS hψA))
  have hUs := hSs U hUS
  have hdisj : C ⊓ U = ⊥ := by
    rcases hSi U hUS (C ⊓ U) inf_le_right (fun x v hv => ⟨hCs x v hv.1, hUs x v hv.2⟩) with h | h
    · exact h
    · exact absurd (inf_eq_right.1 h) hUC
  have hψU := hsup U (hSA U hUS) hUs hUC
  have hAle : A ≤ C ⊔ U := by
    refine hAS.trans (sSup_le fun Y hY => ?_)
    by_cases hYC : Y ≤ C
    · exact hYC.trans le_sup_left
    have hYs := hSs Y hY
    rcases hSi Y hY ((C ⊔ U) ⊓ Y) inf_le_right (fun x v hv => ⟨by
        obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hv.1
        rw [← e, map_add]
        exact Submodule.add_mem_sup (hCs x a ha) (hUs x b hb), hYs x v hv.2⟩) with h | h
    · exfalso
      obtain ⟨c, hc, y, hy, e⟩ := Submodule.mem_sup.1 (hsup Y (hSA Y hY) hYs hYC)
      have hyCU : y ∈ C ⊔ U := by
        have : y = ψ - c := by rw [← e]; abel
        rw [this]
        exact sub_mem hψU (Submodule.mem_sup_left hc)
      have hy0 : y = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (⟨hyCU, hy⟩ : y ∈ (C ⊔ U) ⊓ Y))
      rw [hy0, add_zero] at e
      exact hψC (e ▸ hc)
    · exact inf_eq_right.1 h
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (C ⊔ U)
  have hc : IsCompl U (C ⊔ D) := by
    refine ⟨Submodule.disjoint_def.2 fun u hu hu' => ?_, ?_⟩
    · obtain ⟨c, hc, d, hd, e⟩ := Submodule.mem_sup.1 hu'
      have hdCU : d ∈ C ⊔ U := by
        have : d = u - c := by rw [← e]; abel
        rw [this]
        exact sub_mem (Submodule.mem_sup_right hu) (Submodule.mem_sup_left hc)
      have hd0 : d = 0 := Submodule.disjoint_def.1 hD.disjoint d hdCU hd
      rw [hd0, add_zero] at e
      have : u ∈ C ⊓ U := ⟨e ▸ hc, hu⟩
      rw [hdisj] at this
      exact (Submodule.mem_bot ℂ).1 this
    · rw [codisjoint_iff, ← top_le_iff, ← hD.sup_eq_top]
      exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left) (le_sup_right.trans le_sup_right)
  let pr : V →ₗ[ℂ] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U (C ⊔ D) hc
  have hprU : ∀ u ∈ U, pr u = u := fun u hu =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨u, hu⟩)
  have hprC : ∀ c ∈ C, pr c = 0 := fun c hc' => by
    have h0 : Submodule.linearProjOfIsCompl U (C ⊔ D) hc c = 0 :=
      Submodule.linearProjOfIsCompl_apply_right' hc (Submodule.mem_sup_left hc')
    simp [pr, h0]
  have hform : ∀ c ∈ C, ∀ u ∈ U, pr (c + u) = u := fun c hc' u hu => by
    rw [map_add, hprC c hc', hprU u hu, zero_add]
  refine ⟨U, hUS, pr, ?_, fun f hf => ?_⟩
  · obtain ⟨c, hc', u, hu, e⟩ := Submodule.mem_sup.1 (hAle hψA)
    rw [← e, hform c hc' u hu]
    intro h0
    rw [h0, add_zero] at e
    exact hψC (e ▸ hc')
  · obtain ⟨c, hc', u, hu, rfl⟩ := Submodule.mem_sup.1 (hAle hf)
    refine ⟨by rw [hform c hc' u hu]; exact hu, fun x => ?_⟩
    rw [hform c hc' u hu, map_add, hform _ (hCs x c hc') _ (hUs x u hu)]

theorem embProj_holds : EmbProj := by
  intro E _ _ _ a τ U hU κ hκ u hu hu0
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E a τ
  obtain ⟨r, -, hr1, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints E a τ
  let π : AutSub E a := ⟨U, hU⟩
  let s : Matrix.unitaryGroup (Fin a) ℂ →* UA E a := (embU a τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cEmb τ (s y) = unitaryIncl a y := fun y => by
    have h3 := he (e.symm y)
    rw [e.apply_symm_apply] at h3
    exact h3.symm
  have hirr := isIrreducible_smallRep_unitary a κ
  obtain ⟨-, hsimple⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr
  let S : Set (Submodule ℂ (UA E a → ℂ)) := {V | ∃ F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ), Function.Injective F ∧ (∀ w, F w ∈ U) ∧
    (∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w)) ∧ V = LinearMap.range F}
  have hc : ∀ g, ∃ y, ∀ y', Commute ((s y)⁻¹ * g) (s y') := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU a τ) : UA E a)⁻¹ * g) ((e.symm y : embU a τ) : UA E a)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨f, hf⟩ : ∃ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), f ≠ 0 := by
    obtain ⟨-, F, hF0, hFm, hFi⟩ := hκ
    refine ⟨⟨F.codRestrict U hFm, fun y => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ a κ (unitaryIncl a y) v) = RU E a (s y) (F v)
      rw [← hs y]
      exact hFi (e.symm y) v
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ π.rep s _ _ π.isIrreducible_rep hirr hirr hc f hf).1
  have hUS : U ≤ sSup S := by
    intro φ hφ
    have h1 : (⟨φ, hφ⟩ : U) ∈ (⨆ f : (smallRep (unitaryIncl a) κ).IntertwiningMap (π.rep.comp s), LinearMap.range f.toLinearMap) :=
      htop ▸ Submodule.mem_top
    refine (iSup_le (a := (sSup S).comap U.subtype) fun f' => ?_) h1
    rintro _ ⟨w, rfl⟩
    let F : nablaSq ℂ a κ →ₗ[ℂ] (UA E a → ℂ) := U.subtype ∘ₗ f'.toLinearMap
    have hF : ∀ y w, F (sqRep ℂ a κ (unitaryIncl a y) w) = RU E a (s y) (F w) := fun y w =>
      congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ f' y w)
    show F w ∈ sSup S
    rcases hsimple (LinearMap.ker F) (fun y x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      exact (hF y x).trans (by rw [hx, map_zero])) with h | h
    · exact le_sSup (show LinearMap.range F ∈ S from ⟨F, LinearMap.ker_eq_bot.1 h, fun w => (f' w).2, hF, rfl⟩) ⟨w, rfl⟩
    · have : w ∈ LinearMap.ker F := h ▸ Submodule.mem_top
      rw [LinearMap.mem_ker.1 this]
      exact zero_mem _
  obtain ⟨_, ⟨F, hinj, hFU, hF, rfl⟩, pr, h1, h2⟩ := proj_of_sum (fun y => RU E a (s y)) U S
    (by rintro _ ⟨F, -, hFU, -, rfl⟩ _ ⟨w, rfl⟩; exact hFU w)
    (by rintro _ ⟨F, -, -, hF, rfl⟩ y _ ⟨w, rfl⟩; exact ⟨_, hF y w⟩)
    (by
      rintro _ ⟨F, -, -, hF, rfl⟩ N hN hNs
      rcases hsimple (N.comap F) (fun y x hx => by
        show F _ ∈ N
        exact (hF y x).symm ▸ hNs y _ hx) with h | h
      · left
        rw [eq_bot_iff]
        intro φ hφ
        obtain ⟨w, rfl⟩ := hN hφ
        have : w ∈ N.comap F := hφ
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]
        exact zero_mem _
      · right
        refine le_antisymm hN ?_
        rintro _ ⟨w, rfl⟩
        exact (h ▸ Submodule.mem_top : w ∈ N.comap F))
    hUS u hu hu0
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective F (LinearMap.ker_eq_bot.2 hinj)
  have hGF : ∀ w, G (F w) = w := fun w => LinearMap.congr_fun hG w
  refine ⟨G ∘ₗ pr, fun h0 => h1 ?_, fun x hx y hy => ?_⟩
  · obtain ⟨w, hw⟩ := (h2 u hu).1
    rw [LinearMap.comp_apply, ← hw, hGF] at h0
    rw [← hw, h0, map_zero]
  · obtain ⟨w, hw⟩ := (h2 y hy).1
    have hx' : s (e ⟨x, hx⟩) = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    have h3 := (h2 y hy).2 (e ⟨x, hx⟩)
    rw [← hw, ← hF, ← hs, hx'] at h3
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h3, ← hw, hGF, hGF]

end UpperTheory.Gal.Wt

end
