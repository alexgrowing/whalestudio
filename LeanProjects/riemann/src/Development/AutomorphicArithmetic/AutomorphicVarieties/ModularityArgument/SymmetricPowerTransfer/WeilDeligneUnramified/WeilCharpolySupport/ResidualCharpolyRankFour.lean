import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.GalExW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.CharPolSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.PlainOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.RegUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.EpsAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.UfFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TrPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.BadClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Spread
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.RegElt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TwistOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.AutIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.ExistsNonzeroLowerEntryOfIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.ProjectionComponents.UfDg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowOfRealInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ShapeFacts

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Win UpperTheory.GalN.V
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

private theorem trace_det_of_charpoly_two {k K : Type} [Field k] [Field K] (ι : k ≃+* K) (g : Matrix (Fin 2) (Fin 2) k) (α β : K)
    (h : g.charpoly.map ι.toRingHom = (X - C α) * (X - C β)) : ι g.trace = α + β ∧ ι g.det = α * β := by
  rw [Matrix.charpoly_fin_two] at h
  have e : (X ^ 2 - C (ι g.trace) * X + C (ι g.det) : K[X]) = (X - C α) * (X - C β) := by
    rw [← h]; simp
  have e1 := congrArg (fun p : K[X] => p.coeff 1) e
  have e0 := congrArg (fun p : K[X] => p.coeff 0) e
  have r : (X - C α) * (X - C β) = (X ^ 2 - C (α + β) * X + C (α * β) : K[X]) := by
    simp only [C_add, C_mul]; ring
  rw [r] at e0 e1
  simp [coeff_X, coeff_C] at e0 e1
  exact ⟨by linear_combination -e1, e0⟩

private theorem AuxBlock12 {k K : Type} [Field k] [Field K] (ι : k ≃+* K) (g : Matrix (Fin 3) (Fin 3) k) (α β γ : K)
    (h : g.charpoly.map ι.toRingHom = (X - C α) * (X - C β) * (X - C γ)) : ι g.trace = α + β + γ := by
  have e : ι g.trace = -(g.charpoly.map ι.toRingHom).coeff 2 := by
    rw [Matrix.trace_eq_neg_charpoly_coeff, coeff_map]
    simp
  have r : (X - C α) * (X - C β) * (X - C γ) =
      (X ^ 3 - C (α + β + γ) * X ^ 2 + C (α * β + α * γ + β * γ) * X - C (α * β * γ) : K[X]) := by
    simp only [C_add, C_mul]; ring
  rw [e, h, r]
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  norm_num

private theorem abs_ne_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := fun e => by
  have e' : absPow k (((1 : ℝ) : ℂ)) = absPow k (((0 : ℝ) : ℂ)) := by
    push_cast
    rw [e, absPow_zero]
  have := GlobalTheory.TypeTwo.absPow_ofReal_injective k _ _ e'
  norm_num at this

private theorem unl_two {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : Fin 2 → kˣ →* ℂˣ) (h : Reg (ψ 0 / ψ 1)) (i j : Fin 2) : ψ i ≠ ψ j * absPow k 1 := by
  have two : absPow k 2 = absPow k 1 ^ 2 := by
    rw [pow_two, ← absPow_add]; norm_num
  have h2 := h.2 2 (by norm_num)
  have h3 := h.2 (-2) (by norm_num)
  push_cast at h2 h3
  rw [absPow_neg, two] at h3
  rw [two] at h2
  have n1 := abs_ne_one k
  fin_cases i <;> fin_cases j
  · exact fun e => n1 (by simpa using e)
  · intro e
    apply h2
    simp only [Fin.zero_eta, Fin.mk_one] at e
    rw [e, mul_div_cancel_left]
  · intro e
    apply h3
    simp only [Fin.zero_eta, Fin.mk_one] at e
    rw [e, div_mul_cancel_left, inv_pow]
  · exact fun e => n1 (by simpa using e)

private theorem unl_three {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a : kˣ →* ℂˣ) (h : Reg a) (i j : Fin 3) :
    (![a, 1, a⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ ![a, 1, a⁻¹] j * absPow k 1 := by
  by_cases e : i = j
  · subst e
    exact fun e => abs_ne_one k (by simpa using e)
  · exact ((Al.regUnl k a h).1.2 i j e).2

private theorem local_trace_compatible (P : PrW) {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (r3 : G L Ω →* GL (Fin 3) (Qbar l))
    (σ : Submodule ℂ (UA L 2 → ℂ)) (σ₃ : Submodule ℂ (UA L 3 → ℂ)) (hg : GalT ι σ r) (hg3 : GalT ι σ₃ r3)
    (w : Plc L) (hw : IsSplitAt w) (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (ψ : Fin 2 → (Kw w)ˣ →* ℂˣ) (hE : CompEq σ w ψ)
    (hR : Reg (ψ 0 / ψ 1))
    (hS : CompSub σ₃ w ![ψ 0 / ψ 1, 1, (ψ 0 / ψ 1)⁻¹]) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (t : Weil h) :
    Ga.tr (r3 (t : G L Ω)) * Ga.ep l (t : G L Ω) = Ga.uf (r (t : G L Ω)) + 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds L Ω A w h
  obtain ⟨hsm, τ, hτ, ⟨e⟩⟩ := hE
  obtain ⟨hsm3, τ3, hτ3, hq3⟩ := hS
  have hq2 : IsSubquotient τ.ρ (prinSeries ψ) :=
    IsSubquotient.of_surjective e.symm.toIntertwiningMap e.symm.surjective
  have p2 : PT τ := plainOf P.af.litN L 2 w τ ψ hsm hq2 (unl_two ψ hR)
  have p3 : PT τ3 := plainOf P.af.litN L 3 w τ3 _ hsm3 hq3 (unl_three _ hR)
  have c2 := eigW P.af L Ω l ι 2 r w hl A h a ha τ (hg.loc w hw τ hτ) p2 ψ hsm hq2 t
  have c3 := eigW P.af L Ω l ι 3 r3 w hl A h a ha τ3 (hg3.loc w hw τ3 hτ3) p3 _ hsm3 hq3 t
  have he := (Ga.epsAway P.af L Ω l ι w hl A h a ha t).1
  rw [psPol, Fin.prod_univ_two] at c2
  rw [psPol, Fin.prod_univ_three] at c3
  obtain ⟨t2, d2⟩ := trace_det_of_charpoly_two ι _ _ _ c2
  have t3 := AuxBlock12 ι _ _ _ _ c3
  have hp : (-((((3 : ℕ) : ℂ) - 1) / 2)) = -1 := by norm_num
  rw [hp, absPow_neg] at t3
  apply ι.injective
  simp only [Ga.uf, Ga.tr, map_mul, map_add, map_sub, map_div₀, map_pow, map_one, map_ofNat]
  rw [t2, d2, t3, he]
  simp only [MonoidHom.mul_apply, MonoidHom.div_apply, MonoidHom.inv_apply, MonoidHom.one_apply, Units.val_mul, Units.val_div_eq_div_val,
    Units.val_inv_eq_inv_val, Units.val_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hu := (ψ 0 (a t)).ne_zero
  have hv := (ψ 1 (a t)).ne_zero
  have hq := (absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t)).ne_zero
  have he0 := (absPow (w.adicCompletion L) 1 (a t)).ne_zero
  field_simp
  ring

private theorem irr_of_open {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k}
    (h : IrrOpen r) : IsIrr r := by
  obtain ⟨h1, -, h3⟩ := h ⊤ (by simp)
  exact ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hW => h3 W le_top (fun s v hv => hW s v hv)⟩

private theorem ss_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
    (h : RepIso r r') (hr : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) hr
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

private theorem att_iso {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {π : CuspSub F n}
    (h : RepIso r r') (H : AttC ι r π) : AttC ι r' π :=
  ⟨ss_iso h H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

theorem branch1W : Branch1W := by
  intro Pr L Ω _ _ _ _ _ _ l _ ι hl hU M m hM r σ hA hg P ψ hP hreg σ₃ hσ₃ hev
  obtain ⟨r3, hg3, hirr⟩ := galExW Pr L Ω l ι hl hU 3 (by norm_num) σ₃ hσ₃
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  obtain ⟨hcu, hce, hbad⟩ := Ga.badClosed L Ω l r hg.cont
  have hct : Continuous fun g : G L Ω => Ga.tr (r3 g) :=
    Continuous.matrix_trace (Units.continuous_val.comp hg3.cont)
  let E : Set (G L Ω) := {g | Ga.tr (r3 g) * Ga.ep l g = Ga.uf (r g) + 1 ∧
    Ga.tr (r3 g⁻¹) * Ga.ep l g⁻¹ = Ga.uf (r g⁻¹) + 1}
  have hEc : IsClosed E :=
    IsClosed.inter (isClosed_eq (hct.mul hce) (hcu.add continuous_const))
      (isClosed_eq ((hct.comp continuous_inv).mul (hce.comp continuous_inv)) ((hcu.comp continuous_inv).add continuous_const))
  have hstab : ∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∀ s s' : G L Ω,
      s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ → s' ∈ E → s ∈ E := by
    intro c hc s s' hs hs'
    obtain ⟨h1, h2⟩ := hs'
    obtain ⟨P3, hP3⟩ := hg3.pair c hc
    obtain ⟨P2, hP2⟩ := hg.pair c hc
    have hi : (s'⁻¹ : G L Ω).restrictScalars (maximalRealSubfield L) =
        c * (s⁻¹ : G L Ω).restrictScalars (maximalRealSubfield L) * c⁻¹ := by
      have e : ∀ x : G L Ω, (x⁻¹ : G L Ω).restrictScalars (maximalRealSubfield L) =
          (x.restrictScalars (maximalRealSubfield L))⁻¹ := fun _ => rfl
      rw [e, e, hs]
      group
    have hes : Ga.ep l s' = Ga.ep l s := by
      have e : ∀ x : G L Ω, cycBar L Ω l x = cycBar (maximalRealSubfield L) Ω l (x.restrictScalars (maximalRealSubfield L)) :=
        fun _ => rfl
      simp only [Ga.ep]
      rw [e s', e s, hs, map_mul, map_mul, map_inv, mul_comm (cycBar _ Ω l c), mul_inv_cancel_right]
    have hei : ∀ g : G L Ω, Ga.ep l g⁻¹ = (Ga.ep l g)⁻¹ := by
      intro g
      simp [Ga.ep]
    have hne : Ga.ep l s ≠ 0 := Units.ne_zero _
    have hμ : ∀ g : G L Ω, (((cycBar L Ω l ^ (1 - ((3 : ℕ) : ℤ))) g : (Qbar l)ˣ) : Qbar l) = (Ga.ep l g ^ 2)⁻¹ := by
      intro g
      have e : (1 - ((3 : ℕ) : ℤ)) = -2 := by norm_num
      rw [e]
      simp [Ga.ep, zpow_neg]
    have a1 := Ga.trPair _ 3 (r3 s) (r3 s') P3 _ (hP3 s s' hs)
    have a2 := Ga.trPair _ 3 (r3 s⁻¹) (r3 s'⁻¹) P3 _ (hP3 _ _ hi)
    rw [hμ, ← map_inv] at a1
    rw [hμ, ← map_inv, inv_inv] at a2
    have u1 := (Ga.ufFacts _ (r s)).2.2.2.1 (r s') P2 _ (hP2 s s' hs)
    have u2 : Ga.uf (r s⁻¹) = Ga.uf (r s) := by
      rw [map_inv]
      exact (Ga.ufFacts _ (r s)).2.1
    have u3 : Ga.uf (r s'⁻¹) = Ga.uf (r s') := by
      rw [map_inv]
      exact (Ga.ufFacts _ (r s')).2.1
    refine ⟨?_, ?_⟩
    · rw [u3, u1, a2] at h2
      simp only [hei, hes] at h2
      rw [← h2]
      field_simp
    · rw [a1, hes, u1] at h1
      rw [u2, ← h1, hei]
      field_simp
  have hfrob : ∀ᶠ w in Filter.cofinite, w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E := by
    filter_upwards [hev] with w hw hwP s hs
    obtain ⟨A, hAw, hF⟩ := hs
    obtain ⟨hsp, hlw, hc⟩ := hP.mem w hwP
    have hW := mem_Weil_of_isFrob hAw hF
    exact ⟨local_trace_compatible Pr ι r r3 σ σ₃ hg hg3 w hsp hlw (ψ w) hc (hreg w hwP) (hw hwP) A hAw ⟨s, hW⟩,
      local_trace_compatible Pr ι r r3 σ σ₃ hg hg3 w hsp hlw (ψ w) hc (hreg w hwP) (hw hwP) A hAw ⟨s⁻¹, inv_mem hW⟩⟩
  have hsub := Ga.spread L Ω hU E (Ga.Bad r) hEc hbad hstab P M hM hP.meets hfrob
  obtain ⟨s0, -, hs0, -⟩ := Ga.regElt L Ω l ι M m r hA.toIn ⊤ isOpen_univ
  have hRo : IrrOpen (tw (ad0 r) (cycBar L Ω l)⁻¹) := fun H hH =>
    (Sd.shapeFacts l H 3 ((ad0 r).comp H.subtype) ((cycBar L Ω l)⁻¹.comp H.subtype)).2.2.2.2.2
      (Sd.ad0Irr l (G L Ω) r hg.cont hA.irr H hH)
  have htr : ∀ g ∈ (Ga.Bad r)ᶜ, Ga.tr (r3 g) = Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) :=
    (fun g hg' => by
      have h1 := (hsub hg').1
      have h2 := (Ga.ufFacts _ (r g)).2.2.2.2 _ r g
      have e3 : ((((cycBar L Ω l)⁻¹ g : (Qbar l)ˣ)) : Qbar l) = (Ga.ep l g)⁻¹ := by simp [Ga.ep]
      have hne : Ga.ep l g ≠ 0 := Units.ne_zero _
      have e4 : Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) = (Ga.ep l g)⁻¹ * Ga.tr (ad0 r g) := by
        simp only [Ga.tr, tw_val, Matrix.trace_smul, smul_eq_mul, e3]
      rw [e4, h2, ← h1]
      field_simp)
  obtain ⟨ξ, hξ, hiso⟩ := Ga.twistOf l (G L Ω) 3 (tw (ad0 r) (cycBar L Ω l)⁻¹) r3 hRo (Ga.Bad r)ᶜ hbad.isOpen_compl ⟨s0, hs0⟩ htr
  have h4 := Ga.sym4Irr l (G L Ω) r hg.cont hA.irr fun H hH => by
    obtain ⟨s, hs, -, h⟩ := Ga.regElt L Ω l ι M m r hA.toIn H hH
    exact ⟨s, hs, h⟩
  have hone : ξ = 1 := U.xiOne L Ω l r hg.cont h4 ξ hξ fun g hg' => by
    obtain ⟨x, hx⟩ := hiso
    have h1 := htr g hg'
    have h2 := (Ga.ufFacts _ (r g)).2.2.2.2 _ r g
    have h3 : Ga.tr (r3 g) = (ξ g : Qbar l) * Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) := by
      rw [hx g]
      simp only [Ga.tr]
      rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
        tw_val (tw (ad0 r) (cycBar L Ω l)⁻¹), Matrix.trace_smul, smul_eq_mul]
    have e4 : Ga.tr (tw (ad0 r) (cycBar L Ω l)⁻¹ g) = (((cycBar L Ω l)⁻¹ g : (Qbar l)ˣ) : Qbar l) * Ga.tr (ad0 r g) := by
      simp only [Ga.tr, tw_val, Matrix.trace_smul, smul_eq_mul]
    rw [h3, e4, h2] at h1
    refine mul_left_cancel₀ ((cycBar L Ω l)⁻¹ g).ne_zero ?_
    rw [← h1]
    ring
  have e : tw (tw (ad0 r) (cycBar L Ω l)⁻¹) ξ = tw (ad0 r) (cycBar L Ω l)⁻¹ := by
    ext g : 2
    rw [tw_val, hone]
    simp
  rw [e] at hiso
  have hI := Ga.autIso L Ω l ι 3 _ r3 hiso
  obtain ⟨π, a1, a2, a3, a4⟩ := hirr (irr_of_open (hI.2.2.2.1 hRo))
  exact ⟨π, a1, a2, att_iso hI.2.2.2.2.1 a3, a4⟩

end UpperTheory.V.Z.Sym.W

end
