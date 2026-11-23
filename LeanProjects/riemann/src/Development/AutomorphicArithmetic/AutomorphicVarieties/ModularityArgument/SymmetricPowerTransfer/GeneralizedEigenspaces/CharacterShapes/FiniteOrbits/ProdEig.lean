import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OrbIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Grp

variable {G H : Type} [Group G] [Group H]

private theorem finOrb_one (U : Subgroup G) : AlgebraTools.FinOrb U U (1 : G) := by
  refine Set.Finite.subset (Set.finite_singleton ((1 : G) : G ⧸ U)) ?_
  rintro _ ⟨u, rfl⟩
  refine Set.mem_singleton_iff.2 ?_
  change (((u : G) * 1 : G) : G ⧸ U) = ((1 : G) : G ⧸ U)
  exact QuotientGroup.eq.2 (by simpa using U.inv_mem u.2)

private theorem finOrb_mul (U : Subgroup G) {a b : G} (ha : AlgebraTools.FinOrb U U a) (hb : AlgebraTools.FinOrb U U b) :
    AlgebraTools.FinOrb U U (a * b) := by
  classical
  refine Set.Finite.subset ((Set.Finite.prod ha hb).image
    (fun q : (G ⧸ U) × (G ⧸ U) => ((q.1.out * q.2.out : G) : G ⧸ U))) ?_
  rintro _ ⟨u, rfl⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul U ((u : G) * a)
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul U (((t : G))⁻¹ * b)
  refine ⟨((((u : G) * a : G) : G ⧸ U), ((((t : G))⁻¹ * b : G) : G ⧸ U)), ⟨⟨u, rfl⟩, ⟨t⁻¹, rfl⟩⟩, ?_⟩
  change (((((((u : G) * a : G) : G ⧸ U)).out * ((((t : G))⁻¹ * b : G) : G ⧸ U).out : G)) : G ⧸ U) =
    (((u : G) * (a * b) : G) : G ⧸ U)
  rw [ht, hs]
  have e : (u : G) * a * t * ((t : G)⁻¹ * b * s) = (u : G) * (a * b) * s := by group
  rw [e]
  exact QuotientGroup.mk_mul_of_mem _ s.2

private theorem uf_split (j : H →* G) (p : G →* H) (U : Subgroup G) (hpj : ∀ h, p (j h) = h)
    (hU : ∀ u ∈ U, j (p u) ∈ U) (hC : ∀ u ∈ U, ∀ h, (j (p u))⁻¹ * u * j h = j h * ((j (p u))⁻¹ * u))
    (d : H) (b : G) (hb : ∀ h, b * j h = j h * b) (hpb : p b = 1) : UF U (j d) b := by
  have hv : ∀ u ∈ U, (j (p u))⁻¹ * u ∈ U := fun u hu => U.mul_mem (U.inv_mem (hU u hu)) hu

  have hA : ∀ y ∈ DC U (j d), (j (p y))⁻¹ * y ∈ U := by
    rintro y ⟨u, hu, u', hu', rfl⟩
    have e : (j (p (u * j d * u')))⁻¹ * (u * j d * u') =
        (j (p u'))⁻¹ * ((j d)⁻¹ * (((j (p u))⁻¹ * u) * j d)) * u' := by
      simp only [map_mul, hpj]
      group
    rw [e, hC u hu d, inv_mul_cancel_left]
    exact U.mul_mem (U.mul_mem (U.inv_mem (hU u' hu')) (hv u hu)) hu'
  have hB : ∀ y ∈ DC U b, ∃ m ∈ U, p y = p m := by
    rintro y ⟨u, hu, u', hu', rfl⟩
    exact ⟨u * u', U.mul_mem hu hu', by simp [hpb]⟩
  have key : ∀ g y₁ y₂, y₁ ∈ DC U (j d) → y₂ ∈ DC U (j d) → y₁⁻¹ * g ∈ DC U b → y₂⁻¹ * g ∈ DC U b → y₂⁻¹ * y₁ ∈ U := by
    intro g y₁ y₂ h₁ h₂ k₁ k₂
    obtain ⟨m₁, hm₁, e₁⟩ := hB _ k₁
    obtain ⟨m₂, hm₂, e₂⟩ := hB _ k₂
    have e : p (y₂⁻¹ * y₁) = p (m₂ * m₁⁻¹) := by
      have : y₂⁻¹ * y₁ = (y₂⁻¹ * g) * (y₁⁻¹ * g)⁻¹ := by group
      rw [this, map_mul, map_inv, e₁, e₂, map_mul, map_inv]
    have e' : y₂⁻¹ * y₁ = ((j (p y₂))⁻¹ * y₂)⁻¹ * j (p (m₂ * m₁⁻¹)) * ((j (p y₁))⁻¹ * y₁) := by
      rw [← e]
      simp only [map_mul, map_inv]
      group
    rw [e']
    exact U.mul_mem (U.mul_mem (U.inv_mem (hA _ h₂)) (hU _ (U.mul_mem hm₂ (U.inv_mem hm₁)))) (hA _ h₁)
  intro g
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu, u', hu', rfl⟩
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul U (u * j d)
    have h₁ : (((u * j d : G) : G ⧸ U)).out ∈ DC U (j d) := by
      rw [ht]
      exact ⟨u, hu, t, t.2, rfl⟩
    have h₂ : (((u * j d : G) : G ⧸ U)).out⁻¹ * (u * (j d * b) * u') ∈ DC U b := by
      rw [ht]
      exact ⟨(t : G)⁻¹, U.inv_mem t.2, u', hu', by group⟩
    refine ⟨((u * j d : G) : G ⧸ U), ⟨h₁, h₂⟩, ?_⟩
    rintro y ⟨k₁, k₂⟩
    have := key _ _ _ k₁ h₁ k₂ h₂
    rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' (((u * j d : G) : G ⧸ U))]
    exact (QuotientGroup.eq.2 this).symm
  · rintro y ⟨u, hu, u', hu', rfl⟩ ⟨s, hs, s', hs', e⟩
    have hg : g = u * j d * (u' * s) * b * s' := by
      have : g = (u * j d * u') * ((u * j d * u')⁻¹ * g) := by group
      rw [this, e]
      group
    have hm : u' * s ∈ U := U.mul_mem hu' hs
    set m := u' * s
    set v := (j (p m))⁻¹ * m with hvd
    have hmv : m = j (p m) * v := by simp [hvd]
    have hcomm : v * j (d * p m) = j (d * p m) * v := hC m hm _
    refine ⟨u * v, U.mul_mem hu (hv m hm), j (p m) * s', U.mul_mem (hU m hm) hs', ?_⟩
    have hbm : b * j (p m) = j (p m) * b := hb _
    calc g = u * (j d * j (p m) * v) * b * s' := by rw [hg, hmv]; simp only [mul_assoc, hvd, mul_inv_cancel_left]
      _ = u * (v * j (d * p m)) * b * s' := by rw [hcomm, map_mul j]
      _ = u * v * j d * (j (p m) * b) * s' := by simp only [map_mul, mul_assoc]
      _ = u * v * (j d * b) * (j (p m) * s') := by rw [← hbm]; simp only [mul_assoc]

end Grp

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.prodEig :
    UpperTheory.V.Z.Sym.So.ProdEig := by
  classical
  intro L _ _ _ n U₀ S VL hS hF d
  obtain ⟨hsec, hcomm, -, -, hext, hfi, hfac, hK⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  have hloc0 : ∀ (w : Plc L), ∀ y ∈ locU n w, ∀ u : Plc L, un u ≠ un w → cLoc u y = 1 := fun w y hy u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hy).2 u) hu)
  have hlocF : ∀ (w : Plc L), ∀ y ∈ locU n w, y ∈ finU L n := fun w y hy => (Subgroup.mem_inf.1 hy).1
  have hne : ∀ w ∈ S, ∀ w' ∈ S, w' ≠ w → un w' ≠ un w := fun w hw w' hw' hww e =>
    hww (hS.inj (by exact_mod_cast hw') (by exact_mod_cast hw) e)

  have hlev : ∀ w ∈ S, ∀ u ∈ lev U₀ S VL, secW n w (cLoc w u) ∈ lev U₀ S VL := by
    intro w hw u hu
    have hsp : IsSplitAt w := hS.split w (by exact_mod_cast hw)
    have hu₀ : u ∈ U₀ := (Subgroup.mem_inf.1 hu).1
    have huJ : ∀ w' ∈ S, cLoc w' u ∈ (VL w').J n := fun w' hw' =>
      Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).2 w') hw')
    have huK : cLoc w u ∈ GlobalTheory.LFun.KGL w n :=
      Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hF.1 hu₀)).2 w)
    have htl := (hsec w hsp).1 (cLoc w u)
    have htc := (hsec w hsp).2.1 (cLoc w u)
    have htK : secW n w (cLoc w u) ∈ Kall L n := by
      refine Subgroup.mem_inf.2 ⟨hlocF w _ htl, Subgroup.mem_iInf.2 fun w' => Subgroup.mem_comap.2 ?_⟩
      by_cases h : un w' = un w
      · exact hK w hsp _ (by rw [htc]; exact huK) w' h
      · rw [hloc0 w _ htl w' h]
        exact one_mem _
    refine Subgroup.mem_inf.2 ⟨hF.2 w hw (Subgroup.mem_inf.2 ⟨htl, htK⟩), Subgroup.mem_iInf.2 fun w' =>
      Subgroup.mem_iInf.2 fun hw' => Subgroup.mem_comap.2 ?_⟩
    by_cases h : w' = w
    · subst h
      rw [htc]
      exact huJ _ hw'
    · rw [hloc0 w _ htl w' (hne w hw w' hw' h)]
      exact one_mem _
  have hcm : ∀ w ∈ S, ∀ u ∈ lev U₀ S VL, ∀ h, (secW n w (cLoc w u))⁻¹ * u * secW n w h = secW n w h * ((secW n w (cLoc w u))⁻¹ * u) := by
    intro w hw u hu h
    have hsp : IsSplitAt w := hS.split w (by exact_mod_cast hw)
    have hfu : u ∈ finU L n := (Subgroup.mem_inf.1 (hF.1 (Subgroup.mem_inf.1 hu).1)).1
    obtain ⟨a, hal, hau⟩ := hfac w u hfu
    have haeq : a = secW n w (cLoc w u) := by
      rw [(hsec w hsp).2.2.2 a hal, hau w rfl]
    refine (hcomm w _ ((hsec w hsp).1 h) _ fun u' hu' => ?_).symm.eq
    rw [map_mul, map_inv, ← haeq, hau u' hu', inv_mul_cancel]
  suffices P : ∀ S' : Finset (Plc L), S' ⊆ S → ∀ x : UA L n, OnS S' x → (∀ w ∈ S', cLoc w x = Sig.dg (d w)) →
      AlgebraTools.FinOrb (lev U₀ S VL) (lev U₀ S VL) x ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L n → V),
        (∀ u ∈ lev U₀ S VL, ∀ g, φ (g * u) = φ g) → ∀ c : Plc L → ℂ, (∀ w ∈ S', EigAt φ w (VL w) (d w) (c w)) →
        dcF (lev U₀ S VL) x φ = (∏ w ∈ S', c w) • φ from
    fun x hx hd => P S subset_rfl x hx hd
  intro S'
  induction S' using Finset.induction_on with
  | empty =>
    intro _ x hx _
    have hx1 : x = 1 := hext x 1 (fun w => by rw [hx.2 w (by simp), map_one])
      (fun τ => by rw [(hfi x).1.1 hx.1 τ, map_one])
    subst hx1
    refine ⟨finOrb_one _, fun V _ _ φ hφ c _ => ?_⟩
    have := (dcBasic _ V _ _ (finOrb_one (lev U₀ S VL)) φ hφ).2.2.2.1 (one_mem _)
    simpa using this
  | insert w S'' hw ih =>
    intro hsub x hx hd
    have hwS : w ∈ S := hsub (Finset.mem_insert_self _ _)
    have hsub' : S'' ⊆ S := fun y hy => hsub (Finset.mem_insert_of_mem hy)
    have hsp : IsSplitAt w := hS.split w (by exact_mod_cast hwS)
    have hdw := hd w (Finset.mem_insert_self _ _)
    obtain ⟨a, hal, hax⟩ := hfac w x hx.1
    have haeq : a = secW n w (Sig.dg (d w)) := by
      rw [(hsec w hsp).2.2.2 a hal, hax w rfl, hdw]
    subst haeq
    set a := secW n w (Sig.dg (d w)) with ha
    set b := a⁻¹ * x with hb
    have hxab : x = a * b := by simp [hb]
    have habove : ∀ u : Plc L, un u = un w → cLoc u b = 1 := fun u hu => by
      rw [hb, map_mul, map_inv, hax u hu, inv_mul_cancel]
    have hbOn : OnS S'' b := by
      refine ⟨mul_mem (inv_mem (hlocF w _ hal)) hx.1, fun u hu => ?_⟩
      by_cases h : un u = un w
      · exact habove u h
      · have h1 : cLoc u x = 1 := hx.2 u fun w' hw' => by
          rcases Finset.mem_insert.1 hw' with rfl | hw'
          · exact h
          · exact hu w' hw'
        rw [hb, map_mul, map_inv, h1, hloc0 w _ hal u h]
        simp
    have hbd : ∀ w' ∈ S'', cLoc w' b = Sig.dg (d w') := fun w' hw' => by
      have hww : w' ≠ w := fun e => hw (e ▸ hw')
      rw [hb, map_mul, map_inv, hloc0 w _ hal w' (hne w hwS w' (hsub' hw') hww), hd w' (Finset.mem_insert_of_mem hw')]
      simp
    obtain ⟨ihF, ihE⟩ := ih hsub' b hbOn hbd
    have hFw : Full U₀ {w} := ⟨hF.1, fun w' hw' => by
      rw [Finset.mem_singleton.1 hw']
      exact hF.2 w hwS⟩
    have hat := dcAt L n U₀ S VL hS w hwS hFw (d w)
    have hUF : UF (lev U₀ S VL) a b :=
      uf_split (secW n w) (cLoc w) (lev U₀ S VL) (hsec w hsp).2.1 (hlev w hwS) (hcm w hwS) (Sig.dg (d w)) b
        (fun h => (hcomm w _ ((hsec w hsp).1 h) b habove).symm.eq) (by
          exact habove w rfl)
    have hFab := finOrb_mul (lev U₀ S VL) hat.1 ihF
    rw [hxab]
    refine ⟨hFab, fun V _ _ φ hφ c hc => ?_⟩
    have hsm : dcF (lev U₀ S VL) a ((∏ w ∈ S'', c w) • φ) = (∏ w ∈ S'', c w) • dcF (lev U₀ S VL) a φ :=
      map_smul (dc (rightReg ℂ (UA L n) V) (lev U₀ S VL) (lev U₀ S VL) a) _ φ
    rw [← uFMul _ V _ a b hat.1 ihF hFab hUF φ hφ, ihE V φ hφ c fun w' hw' => hc w' (Finset.mem_insert_of_mem hw'),
      hsm, (hat.2 V φ hφ (c w)).1 (hc w (Finset.mem_insert_self _ _)), smul_smul, Finset.prod_insert hw, mul_comm]

end
