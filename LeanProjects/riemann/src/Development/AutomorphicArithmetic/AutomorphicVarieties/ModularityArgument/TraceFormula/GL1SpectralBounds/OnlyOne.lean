import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.CuspOrTwoAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LPermSub
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EventuallySatV
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Strong
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.BlockTheory.IrreducibleCharacters.CuspidalCharacters

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F UpperTheory.V.Z.Tf.GOne

namespace UpperTheory.V.Z.Tf.GOne.saturation_regularity_aux

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

private theorem hasSat_of_comp {P : CuspSub E n} (hV : IsDiscrete P.V) {w : HeightOneSpectrum (𝓞 E)}
    {σ : SmIrr (GL (Fin n) (w.adicCompletion E))} (hσ : IsLocCompGL P.V w σ) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) : GlobalTheory.LFun.HasSatGL w (P.locRep w) B := by
  have hmem : ∀ ψ ∈ P.V, ψ ∈ ⨆ f : SatakeVectors.SatakeVectorEventually.MapsD P.V w σ, LinearMap.range f.1 := fun ψ hψ => by
    rw [SatakeVectors.SatakeVectorEventually.iSup_range_eq hV w σ hσ]; exact hψ
  constructor
  · obtain ⟨f, h0, hfV, hf⟩ := hσ
    obtain ⟨x, hx⟩ := hB.exists_vec
    have hi : LinearMap.ker f = ⊥ := ((GlobalTheory.IndefiniteRowSideFullHecke.CuspidalCharacters.isIrreducible_iff σ.ρ).1 σ.irred).2 _ (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, hv, map_zero]) |>.resolve_right fun e => h0 (LinearMap.ker_eq_top.1 e)
    have h1 := hx.map (ρ' := (finRep E n).comp (locGL E n w)) f hf
      ((map_ne_zero_iff f (LinearMap.ker_eq_bot.1 hi)).2 hx.1)
    refine (Submodule.ne_bot_iff _).2 ⟨⟨f x, hfV x⟩, GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_,
      fun e => h1.1 (congrArg Subtype.val e)⟩
    exact GlobalTheory.LGrp.mem_fixed.1 h1.2.1 k hk
  · intro y hy h0
    have h2 := GlobalTheory.HeightCounting.Blocks.isSatVecGL_of_mem_iSup (ρ := (finRep E n).comp (locGL E n w)) σ.irred hB
      (fun f : SatakeVectors.SatakeVectorEventually.MapsD P.V w σ => f.1) (fun f => f.2.2) (hmem y.1 y.2)
      (GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hy k hk))
      (fun e => h0 (Subtype.ext e))
    exact GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E n).comp (locGL E n w)) P.V.subtype (fun _ _ => rfl)
      Subtype.val_injective h2

private theorem regInt_of_weight {V : Submodule ℂ (Sm E n)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (lam : Formalism.BasicNotions.DomWeight n) (e : m = infOfWeight lam) : RegInt V τ := by
  subst e
  refine ⟨_, h, GlobalTheory.DefiniteBC.nodup_infOfWeight lam, fun x hx y hy => ?_⟩
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨l, -, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨lam.w k - lam.w l - (k : ℕ) + (l : ℕ), by push_cast; ring⟩

private theorem key (hC : CuspOrTwo) (hT : NotTwo) {m : ℕ} (hn : 1 ≤ n) (π : CuspSub E n) (hm : m = n)
    {V : Submodule ℂ (Sm E m)} (σ : ∀ w : HeightOneSpectrum (𝓞 E), SmIrr (GL (Fin m) (w.adicCompletion E)))
    (mu : (E →+* ℂ) → Multiset ℂ) (hV : IsDiscrete V) (hl : ∀ w, IsLocCompGL V w (σ w))
    (hi : ∀ τ, HasInfCharGL V τ (mu τ)) (hr : ∀ τ, ∃ lam : Formalism.BasicNotions.DomWeight n, mu τ = infOfWeight lam)
    (hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ B, GlobalTheory.LFun.HasSatGL w (σ w).ρ B ∧ (CG.mk π).HasSat w B) :
    ∃ e : m = n, e ▸ V = π.V := by
  subst hm
  refine ⟨rfl, ?_⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨lam, hlam⟩ := hr τ
  rcases hC E m hn V hV τ (regInt_of_weight (hi τ) lam hlam) with ⟨P, rfl⟩ | ⟨a, d, P, ha, hd, -, -, hA⟩
  · exact UpperTheory.V.Af.strongMultOneC E m P π
      (hs.mono fun w ⟨B, h1, h2⟩ => ⟨B, hasSat_of_comp hV (hl w) h1, h2⟩)
  · exact absurd (hs.mono fun w ⟨B, h1, h2⟩ => ⟨σ w, B, hl w, h1, h2⟩) (hT E m a d V P π ha hd hV hA)

end UpperTheory.V.Z.Tf.GOne.saturation_regularity_aux

theorem UpperTheory.V.Z.Tf.GOne.onlyOne :
    CuspOrTwo → NotTwo → OneSat → OnlyOne := by
  intro hC hT hS E _ _ _ n hn π D D' e hR h1 hcls
  have hc : D.c = 1 := by
    have h := Fintype.card_congr e
    simp only [Fintype.card_fin] at h
    rw [h]
    exact h1.1
  refine ⟨hc, fun i => ?_⟩
  have hsum : ∀ {M : Type} [AddCommMonoid M] (f : Fin D.c → M), ∑ j, f j = f i := fun {M} _ f => by
    have hsub : Subsingleton (Fin D.c) := by rw [hc]; infer_instance
    exact Fintype.sum_subsingleton f i
  have hN : D.N i = n := (hsum D.N).symm.trans D.h
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ B, GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ B ∧ (CG.mk π).HasSat w B := by
    filter_upwards [Rig.eventually_sat D] with w hw
    obtain ⟨S, hS1, -⟩ := hw
    have hB : D.Sat w (∑ j, S j) := ⟨S, fun j => hS1 j, rfl⟩
    refine ⟨S i, (hS1 i).2, ?_⟩
    rw [← hsum S]
    exact (hS E n hn π D' h1 w _).2 (Rig.permSat E n D D' e w (fun j => hcls j w) _ hB)
  have hreg : ∀ τ, ∃ lam : Formalism.BasicNotions.DomWeight n, D.m i τ = infOfWeight lam := fun τ =>
    (hR τ).imp fun lam h => (hsum (D.m · τ)).symm.trans h
  exact saturation_regularity_aux.key hC hT hn π hN (D.σ i) (D.m i) (D.discrete i) (D.loc i) (D.inf i) hreg hsat
