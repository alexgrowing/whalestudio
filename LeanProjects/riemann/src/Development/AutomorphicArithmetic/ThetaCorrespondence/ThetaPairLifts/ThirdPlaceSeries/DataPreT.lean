import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometryColumn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LevPrimeData
open GlobalTheory.FinPl GlobalTheory.FinPl.FrameLat
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.LevPrimeData
theorem GlobalTheory.LevPrimeData.data_preT_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u g)) (ζ₀ : Fin g.Lz.rank → (I.rec7 l Z).host.E), GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ g.x g.vac c₀ → v.NT = (_root_.GlobalTheory.Fam.pk_z W).ΛX → (∀ p, p ∈ v.tP ↔ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.asIdeal) → IsLineVec g.Lz ζ₀ → (∀ r, vecB (g.oT B.R.m rfl) ζ₀ r = (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)) → GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (∀ x : GlobalTheory.FinPl.Pl (I.rec7 l Z), ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ x.asIdeal → ∃ LZ : GlobalTheory.FinPl.Lat g.Lz, GlobalTheory.FinPl.OrthAt (g.oT B.R.m rfl) (g.x B.R.m).L (_root_.GlobalTheory.Fam.pk_z W).ΛX LZ x) → (∀ j h, (v.τ j h)ᴴ * ((g.bes j 0 h).L.gram * v.τ j h) = (-((I.rec7 l Z).host.xi0 * star (I.rec7 l Z).host.xi0)) • g.Lz.gram ∧ v.τ j h *ᵥ ζ₀ = (-(I.rec7 l Z).host.xi0 ^ (B.R.m / 2)) • (g.bes j 0 h).ζ) → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u g) k ι), PreT v o ∧ o.ζ₀ = ζ₀ ∧ GlobalTheory.AdForm.StdT I l Z u o.p o.β o.Q fun j => (g.x j).L := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u g c₀ v ζ₀ hPin hNT htP hline hz hemb hort htau
  obtain ⟨pins⟩ := hW.tr.pins
  obtain ⟨k, _, _, _, _, ι, p, J, q, χ, β, Q, hPl, hch, -, hval, hpl, hb, hStd⟩ :=
    GlobalTheory.T.standardPairs_exist_at_levelPrime I hW.tr.ok pins l Z u (_root_.GlobalTheory.Fam.pk_z W).ψ hPin.std (fun j => (g.x j).L) (fun j hj z => (hPin.xs j hj).2.2 z)
  have hG : ∀ j, ((I.rec7 l Z).sp.X j).gram = 1 := fun j => hW.tr.ok.gram_X j
  have hz' : ∀ r : Fin ((I.rec7 l Z).sp.X B.R.m).rank, vecB (g.oT B.R.m rfl) ζ₀ r =
      if r.1 + 1 = ((I.rec7 l Z).sp.X B.R.m).rank then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0 := by
    intro r
    rw [hz r]
    have e : ((I.rec7 l Z).sp.X B.R.m).rank = B.R.N B.R.m := Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl
    show (if r.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) = _
    rw [← e]
  have hpos : 0 < ((I.rec7 l Z).sp.X B.R.m).rank := by
    have h1 := (g.oT B.R.m rfl).rank_add
    have h2 : g.Lz.rank = 1 := hline.1
    omega
  have htop := fun i => GlobalTheory.StdPairTop.ker_stdPair _ k (p i) q _ _ _ (g.oT B.R.m rfl) (hG _) ζ₀ hline (X.piT u) _ hz' (hval i).1 (hval i).2
    (g.x B.R.m).L v.NT (fun z => (hPin.xs _ le_rfl).2.2 z)
    (by obtain ⟨LZ, h⟩ := hort (p i).v ((hpl _).1 ⟨i, rfl⟩); exact ⟨LZ, hNT ▸ h⟩)
    (β B.R.m i) (Q B.R.m i) (hb _ _) ((hStd.2 _ le_rfl).2 i).1 ((hStd.2 _ le_rfl).2 i).2
  choose γ γ₀ hγ using htop
  have hcore : ∀ j ρ h i, Nonempty (GlobalTheory.FinPl.Frame (p i) (g.bes j ρ h).V₀ (Fin ((I.rec7 l Z).sp.X j).rank ⊕ Fin 1)) := by
    intro j ρ h i
    obtain ⟨γ', -⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character _).2 k (p i)).1 (g.bes j ρ h).V₀ (Fin (g.bes j ρ h).V₀.rank) 1 1
      (Matrix.mul_one _) (Matrix.mul_one _)
    obtain ⟨α, -⟩ := ((GlobalTheory.T.exists_splitPoint_frame_character _).2 k (p i)).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1
      (Matrix.mul_one _) (Matrix.mul_one _)
    obtain ⟨β₀, -⟩ := GlobalTheory.FinPl.DblInh.exists_sumFrame (g.bes j ρ h).o (g.bes j ρ h).line α γ'
    exact ⟨β₀⟩
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, ι,
    ⟨p, J, q, χ, fun i => (hch i).1, β, Q, fun j ρ h i => (hcore j ρ h i).some, fun _ _ _ => ⊥, ζ₀, γ,
      fun n h i => h ▸ γ₀ i⟩, ?_, rfl, hStd⟩
  refine ⟨hPl.nodup, hPl.all, hPl.inj, fun x => (htP x).trans (hpl x).symm, fun i => ⟨(hch i).2, hPl.unit i⟩,
    fun j hj i => ((hStd.2 j hj).2 i).1, hline, fun j h => (htau j h).1,
    fun j h => ⟨_, (htau j h).2, fun i => GlobalTheory.LevPrimeData.splitPlace_valuation_neg_cmGenerator_pow_eq_one (p i) (hPl.unit i) _⟩,
    fun i => GlobalTheory.MiStar.normLast_valuation _ k (p i) q _ _ _ (g.oT B.R.m rfl) hpos (hG _) ζ₀ _ hz' (hval i).1 (hval i).2, fun n h i => ?_⟩
  subst h
  obtain ⟨h1, Λ, s, h2, h3, h4⟩ := hγ i
  exact ⟨h1, Λ, s, hNT ▸ h2, h3, h4⟩
end
