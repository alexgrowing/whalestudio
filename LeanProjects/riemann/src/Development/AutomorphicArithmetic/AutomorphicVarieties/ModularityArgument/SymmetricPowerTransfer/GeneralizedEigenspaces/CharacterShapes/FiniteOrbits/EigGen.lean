import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.ValInvGe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ConjMemLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DetRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinToAF
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSubgroupOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.HomTrivialOnDetOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So.OS

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private def eG {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) : H ≃* ↥((SUA L).subgroupOf (finU L 2)) := E.trans eT

private def psi {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {V : Type} (ψ : H → V) (s : ↥((SUA L).subgroupOf (finU L 2))) : V := ψ ((eG E).symm s)

private theorem psi_e {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {V : Type} (ψ : H → V) (g : H) : psi E ψ (eG E g) = ψ g := by
  show ψ ((eG E).symm (eG E g)) = _
  rw [MulEquiv.symm_apply_apply]

private instance : (finU L 2).Normal := by unfold finU; infer_instance

private theorem out_gen {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) (p : UA L 2 →* finU L 2)
    (hp1 : ∀ f : finU L 2, ∀ k ∈ infU L 2, p ((f : UA L 2) * k) = f)
    (hp2 : ∀ x : UA L 2, ∃ k ∈ infU L 2, x = (p x : UA L 2) * k)
    {m : ℕ} (hm : 3 ≤ m) {U : Subgroup (UA L 2)} (hU : IsCong m U) (U₁ : Subgroup (UA L 2)) (hU₁ : U₁ ≤ U) (hfin : U₁ ≤ finU L 2)
    {n : ℕ} (ψ : H → Wt.VD (InfinitePlace L) n)
    (hleft : ∀ (γ : ratU L 2) (g g' : ↥((SUA L).subgroupOf (finU L 2))), (g' : finU L 2) = p γ.1 * g →
      psi E ψ g' = repE n (0 : InfinitePlace L → ℤ) (infC L 2 γ.1) (psi E ψ g))
    (hright : ∀ u : ↥((SUA L).subgroupOf (finU L 2)), (u : finU L 2) ∈ U₁.subgroupOf (finU L 2) → ∀ g, psi E ψ (g * u) = psi E ψ g) :
    ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) n, IsAF (repE n (0 : InfinitePlace L → ℤ)) U₁ φ ∧ (∀ g : H, φ (E g : UA L 2) = ψ g) ∧
      ∀ (a : ↥((SUA L).subgroupOf (finU L 2))) (c : ℂ), AlgebraTools.FinOrb U₁ U₁ ((a : finU L 2) : UA L 2) →
        AlgebraTools.FinOrb (U₁.subgroupOf (finU L 2)) (U₁.subgroupOf (finU L 2)) (a : finU L 2) →
        (∀ u ∈ U₁.subgroupOf (finU L 2), ∃ z ∈ U₁.subgroupOf (finU L 2), z * (a : finU L 2) = a * z ∧
          u * z⁻¹ ∈ (SUA L).subgroupOf (finU L 2) ∧ z⁻¹ * u ∈ (SUA L).subgroupOf (finU L 2)) →
        dcF ((U₁.subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))) a (psi E ψ) = c • psi E ψ →
        dcF U₁ ((a : finU L 2) : UA L 2) φ = c • φ := by
  have hroot : ∀ γ : ratU L 2, ∀ u ∈ U₁.subgroupOf (finU L 2),
      (p.comp (ratU L 2).subtype) γ * u ∈ (SUA L).subgroupOf (finU L 2) → (p.comp (ratU L 2).subtype) γ ∈ (SUA L).subgroupOf (finU L 2) := by
    intro γ u hu h
    obtain ⟨k, hk, hγ⟩ := hp2 γ.1
    have hr : (p γ.1 : UA L 2) * k ∈ ratU L 2 := by rw [← hγ]; exact γ.2
    exact Subgroup.mem_subgroupOf.2 (detRoot L m hm U hU _ (p γ.1).2 k hk hr u
      (hU₁ (Subgroup.mem_subgroupOf.1 hu)) (Subgroup.mem_subgroupOf.1 h)).1
  obtain ⟨Φ, hΦ1, hΦ2, hΦ3, hΦ4⟩ := extF (ratU L 2) (finU L 2) (Wt.VD (InfinitePlace L) n) (p.comp (ratU L 2).subtype)
    ((repE n (0 : InfinitePlace L → ℤ)).comp ((infC L 2).comp (ratU L 2).subtype))
    ((SUA L).subgroupOf (finU L 2)) (U₁.subgroupOf (finU L 2)) comm_mem hroot (psi E ψ) hleft hright
  obtain ⟨φ, hAF, hφ2, hφ3⟩ := finToAF L 2 (Wt.VD (InfinitePlace L) n) (repE n (0 : InfinitePlace L → ℤ)) U₁ hfin Φ
    (by
      intro f k hk hr g
      have h₁ := hΦ2 ⟨_, hr⟩ g
      have e₁ : (p.comp (ratU L 2).subtype) ⟨_, hr⟩ = f := hp1 f k hk
      rw [e₁] at h₁
      rw [h₁]
      show repE n (0 : InfinitePlace L → ℤ) (infC L 2 ((f : UA L 2) * k)) _ = _
      rw [map_mul, infC_fin f.2, one_mul])
    (fun u hu g => hΦ3 u (Subgroup.mem_subgroupOf.2 hu) g)
  refine ⟨φ, hAF, fun g => ?_, fun a c h₁ h₂ h₃ h₄ => hφ3 a c h₁ (hΦ4 a c h₂ h₃ h₄)⟩
  exact (hφ2 (eG E g : finU L 2)).trans ((hΦ1 (eG E g)).trans (psi_e E ψ g))

private theorem eig_gen {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {S₁ : Finset (Plc L)} (hpl₁ : Places (S₁ : Set (Plc L)))
    {U : Subgroup (UA L 2)} (hFull : Full U S₁) {n : ℕ} (ψ : H → Wt.VD (InfinitePlace L) n)
    (hright : ∀ u : ↥((SUA L).subgroupOf (finU L 2)), (u : finU L 2) ∈ ((lev U S₁ iw).subgroupOf (finU L 2)) → ∀ g, psi E ψ (g * u) = psi E ψ g)
    (φ : UA L 2 → Wt.VD (InfinitePlace L) n) (hφi : ∀ u ∈ lev U S₁ iw, ∀ g, φ (g * u) = φ g)
    (hφ : ∀ (a : ↥((SUA L).subgroupOf (finU L 2))) (c : ℂ), AlgebraTools.FinOrb (lev U S₁ iw) (lev U S₁ iw) ((a : finU L 2) : UA L 2) →
        AlgebraTools.FinOrb ((lev U S₁ iw).subgroupOf (finU L 2)) ((lev U S₁ iw).subgroupOf (finU L 2)) (a : finU L 2) →
        (∀ u ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), ∃ z ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), z * (a : finU L 2) = a * z ∧
          u * z⁻¹ ∈ ((SUA L).subgroupOf (finU L 2)) ∧ z⁻¹ * u ∈ ((SUA L).subgroupOf (finU L 2))) →
        dcF (((lev U S₁ iw).subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))) a (psi E ψ) = c • psi E ψ →
        dcF (lev U S₁ iw) ((a : finU L 2) : UA L 2) φ = c • φ)
    {w : Plc L} (hw : w ∈ S₁) (d₀ : Fin 2 → (Kw w)ˣ) (c : ℂ) (g : H) (hsec : (E g : UA L 2) = secW 2 w (Sig.dg d₀))
    (hoff : ∀ u, un u ≠ un w → cLoc u (E g : UA L 2) = 1) (d : ∀ w : Plc L, Fin 2 → (Kw w)ˣ)
    (hcl : ∀ w' ∈ S₁, cLoc w' (E g : UA L 2) = Sig.dg (d w'))
    (hE : dcF (((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap E.toMonoidHom) g ψ = c • ψ) : EigAt φ w (iw w) d₀ c := by
  have hUfin : lev U S₁ iw ≤ finU L 2 := fun x hx => (hFull.1 hx.1).1
  have hFw : Full U {w} := ⟨hFull.1, fun w' h' => hFull.2 w' (by rw [Finset.mem_singleton.1 h']; exact hw)⟩
  have hdc := dcAt L 2 U S₁ iw hpl₁ w hw hFw d₀
  have hfo := hdc.1
  refine (hdc.2 _ φ hφi _).2 ?_
  rw [← hsec] at hfo ⊢
  have hz : ∀ u ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), ∃ z ∈ ((lev U S₁ iw).subgroupOf (finU L 2)), z * (eG E g : finU L 2) = (eG E g : finU L 2) * z ∧
      u * z⁻¹ ∈ ((SUA L).subgroupOf (finU L 2)) ∧ z⁻¹ * u ∈ ((SUA L).subgroupOf (finU L 2)) := by
    intro u hu
    obtain ⟨c₀, hc₀, h₁, h₂, h₃⟩ := torUA L U S₁ iw hpl₁ hFull u (Subgroup.mem_subgroupOf.1 hu)
    have hcm := h₃ (E g : UA L 2) d ⟨(E g).2.1, fun u' hu' => hoff u' (hu' w hw)⟩ hcl
    exact ⟨⟨c₀, hUfin hc₀⟩, Subgroup.mem_subgroupOf.2 hc₀, Subtype.ext hcm, Subgroup.mem_subgroupOf.2 h₁.2, Subgroup.mem_subgroupOf.2 h₂.2⟩
  have hfo' : AlgebraTools.FinOrb ((lev U S₁ iw).subgroupOf (finU L 2)) ((lev U S₁ iw).subgroupOf (finU L 2)) (eG E g : finU L 2) :=
    (dcSub (UA L 2) ℂ (finU L 2) (lev U S₁ iw) (eG E g : finU L 2) hfo
      (fun u hu => ⟨1, one_mem _, by rw [mul_one, one_mul], by rw [inv_one, mul_one]; exact hUfin hu, by rw [inv_one, one_mul]; exact hUfin hu⟩) inferInstance).1
  have hfo'' := (dcSub (finU L 2) ℂ ((SUA L).subgroupOf (finU L 2)) ((lev U S₁ iw).subgroupOf (finU L 2)) (eG E g) hfo' hz inferInstance).1
  refine hφ (eG E g) _ hfo hfo' hz ?_
  have hmp := (dcMap H ↥((SUA L).subgroupOf (finU L 2)) (Wt.VD (InfinitePlace L) n) (eG E).toMonoidHom (eG E).bijective (((lev U S₁ iw).subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))) g g).2.2.2 hfo'' (psi E ψ)
    (fun u hu g' => hright u (Subgroup.mem_subgroupOf.1 hu) g')
  have hψE : psi E ψ ∘ (eG E).toMonoidHom = ψ := funext fun g' => psi_e E ψ g'
  have hcmp : (((lev U S₁ iw).subgroupOf (finU L 2)).subgroupOf ((SUA L).subgroupOf (finU L 2))).comap (eG E).toMonoidHom = ((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap E.toMonoidHom :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hψE, hcmp, hE] at hmp
  funext s
  obtain ⟨g', rfl⟩ := (eG E).surjective s
  have h₅ := congrFun hmp g'
  refine h₅.symm.trans ?_
  show c • ψ g' = c • psi E ψ (eG E g')
  rw [psi_e]

private theorem all_gen {H : Type} [Group H] (E : H ≃* ↥(finU L 2 ⊓ SUA L)) {S₁ : Finset (Plc L)} (hpl₁ : Places (S₁ : Set (Plc L)))
    {m : ℕ} (hm : 3 ≤ m) {U : Subgroup (UA L 2)} (hU : IsCong m U) (hFull : Full U S₁) {n : ℕ} (ψ : H → Wt.VD (InfinitePlace L) n) (hψ : ψ ≠ 0)
    (p : UA L 2 →* finU L 2) (hp1 : ∀ f : finU L 2, ∀ k ∈ infU L 2, p ((f : UA L 2) * k) = f)
    (hp2 : ∀ x : UA L 2, ∃ k ∈ infU L 2, x = (p x : UA L 2) * k)
    (hleft : ∀ (γ : ratU L 2) (g g' : ↥((SUA L).subgroupOf (finU L 2))), (g' : finU L 2) = p γ.1 * g →
      ψ ((E.trans eT).symm g') = repE n (0 : InfinitePlace L → ℤ) (infC L 2 γ.1) (ψ ((E.trans eT).symm g)))
    (hlv : ∀ u : H, (E u : UA L 2) ∈ lev U S₁ iw → ∀ g, ψ (g * u) = ψ g) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ)
    (hel : ∀ w ∈ S₁, ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 → ∃ (g : H) (d : ∀ w : Plc L, Fin 2 → (Kw w)ˣ),
      (E g : UA L 2) = secW 2 w (Sig.dg ![t, t⁻¹]) ∧ (∀ u, un u ≠ un w → cLoc u (E g : UA L 2) = 1) ∧
      (∀ w' ∈ S₁, cLoc w' (E g : UA L 2) = Sig.dg (d w')) ∧
      dcF (((lev U S₁ iw).subgroupOf (finU L 2 ⊓ SUA L)).comap E.toMonoidHom) g ψ = Dict.expo ![a w, 1] ![t, t⁻¹] • ψ) :
    ∃ φ : UA L 2 → Wt.VD (InfinitePlace L) n, φ ≠ 0 ∧ IsAF (repE n 0) (lev U S₁ iw) φ ∧ ∀ w ∈ S₁, Dict.EigS φ w (iw w) (a w) := by
  have hUle : lev U S₁ iw ≤ U := fun x hx => hx.1
  have hUfin : lev U S₁ iw ≤ finU L 2 := fun x hx => (hFull.1 hx.1).1
  have hright : ∀ u : ↥((SUA L).subgroupOf (finU L 2)), (u : finU L 2) ∈ ((lev U S₁ iw).subgroupOf (finU L 2)) → ∀ g, psi E ψ (g * u) = psi E ψ g := by
    intro u hu g
    show ψ ((eG E).symm (g * u)) = ψ ((eG E).symm g)
    rw [map_mul]
    refine hlv _ ?_ _
    show (((eG E ((eG E).symm u) : ↥((SUA L).subgroupOf (finU L 2))) : finU L 2) : UA L 2) ∈ lev U S₁ iw
    rw [MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hu
  obtain ⟨φ, hAF, hval, hφ⟩ := out_gen E p hp1 hp2 hm hU (lev U S₁ iw) hUle hUfin ψ hleft hright
  have hne : φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 hψ
    intro h
    exact hg (by rw [← hval, h]; rfl)
  refine ⟨φ, hne, hAF, fun w hw t ht => ?_⟩
  obtain ⟨g, d, h1, h2, h3, h4⟩ := hel w hw t ht
  exact eig_gen E hpl₁ hFull ψ hright φ hAF.level hφ hw _ _ g h1 h2 d h3 h4

end UpperTheory.V.Z.Sym.So.OS

set_option allowUnsafeReducibility true in
attribute [local irreducible] DX KD RP SA

open UpperTheory.V.Z.Sym.So.OS in
set_option maxHeartbeats 2000000 in
theorem UpperTheory.V.Z.Sym.So.outS :
    UpperTheory.V.Z.Sym.So.OutS := by
  intro L _ _ _ B hB T S VL A hA hF S₁ hS₁ hiw m U hm hU hFull n e a b hab ι hι y hy hlev ψ hψ hSF
  classical
  obtain ⟨p, hp1, hp2⟩ := exFin (L := L) 2
  have hpl₁ : Places (S₁ : Set (Plc L)) :=
    ⟨fun w' hw' => hF.pl.split w' (hS₁ hw'), hF.pl.inj.mono (by exact_mod_cast hS₁)⟩
  have h1 := left_eq B hB p hp1 hp2 hm hU ι hι (e := e) ψ hSF.left
  refine all_gen B.bS hpl₁ hm hU hFull ψ hψ p hp1 hp2 h1 (fun u hu => hSF.level u (hlev u hu)) a fun w hw t ht => ?_
  have hwS := hS₁ hw
  have h := hF.pl.split w hwS
  have hFw : Full U {w} := ⟨hFull.1, fun w' h' => hFull.2 w' (by rw [Finset.mem_singleton.1 h']; exact hw)⟩
  refine (place_el hB T hA hF hab hwS h t ht).elim fun t' H1 => H1.elim fun g H => ?_
  have hsl := sLev L B hB T S VL A hA hF w hwS h S₁ hw hS₁ (hiw w hw) U hFw y hy hlev _ ψ hSF.level g ![t, t⁻¹] H.2.2.2.1
  have he := hSF.eig t' g H.2.1 H.1
  exact ⟨g, fun w' => if h' : IsSplitAt w' then fun i => iu T w' h' (SD.dS t' (un w') i) else 1, H.2.2.2.1, H.2.2.2.2.1,
    fun w' hw' => (H.2.2.2.2.2 w' (hS₁ hw') (hF.pl.split w' (hS₁ hw'))).trans (by beta_reduce; rw [dif_pos (hF.pl.split w' (hS₁ hw'))]),
    hsl.trans (he.trans (congrArg (· • ψ) H.2.2.1))⟩

end
