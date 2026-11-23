import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.StabZero

open GlobalTheory.Mem.Col2.ClsZero

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem idx_empty (a : I.ι) (u : B.Word) {b : (I.stp u a 0).β} (p : (I.stp u a 0).D b) : p.1.2 = ∅ := by
  obtain ⟨⟨q, Y⟩, hY⟩ := p
  rw [ys0 a] at hY
  exact hY

theorem gam_eq_one (h : I.Ok) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1)
    (c : (I.stp u a 0).Cl) (s : (I.stp u a 0).Stab c) : s.1.1 = 1 := by
  obtain ⟨b⟩ := stepZero_chartIndex_nonempty h a
  obtain ⟨c', rfl⟩ := (bij0 h u a b).2 c
  have hd := stepZero_corresponding_representatives_same_deco h u a b c'
  set p := (I.stp u a 0).rep (I.cl0 u a b c') with hp
  set p0 := (I.stp u I.mu0 0).rep c' with hp0
  have hs : _ = _ := s.2
  have hsd : ((s.1.1, (s.1.2.1.1 : GLG B.fields.E (B.R.N 0) (B.primes X).vGs)) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • p.1.1.deco = p.1.1.deco :=
    congrArg (fun x => DecoF.deco x.1.1) hs
  rw [hd] at hsd
  have hγ : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (z : Sp B.fields.E (B.R.N 0)),
      s.1.1.1 z ∈ p0.1.1.deco.1.at P ↔ z ∈ p0.1.1.deco.1.at P := by
    intro P z
    have e := congrArg (fun d : DecoSet B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs => s.1.1.1 z ∈ d.1.at P) hsd
    simp only at e
    rw [← e]
    show s.1.1.1 z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap s.1.1.1 _) ↔ _
    rw [mem_localization_gmap, LinearEquiv.symm_apply_apply]
  have hc : ∀ P, ((p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P)) ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    show (p0.1.1.1.2 P).symm (s.1.1.1 (p0.1.1.1.2 P x)) ∈ stdAt _ _ P.1 ↔ x ∈ stdAt _ _ P.1
    rw [← p0.1.1.2 P, LinearEquiv.apply_symm_apply, ← p0.1.1.2 P x]
    exact hγ P.1 _
  let t : (I.stp u I.mu0 0).G c'.1 :=
    (s.1.1, ⟨s.1.2.1.1, by
      have e1 := levelTypePrimes_stepZero_eq_colLev h I.mu0 c'.1
      have e2 := levelTypePrimes_stepZero_eq_colLev h a b
      rw [e1, ← e2]
      exact s.1.2.1.2⟩,
     ⟨fun P => ⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩, by
      rw [chartIndexLevelTwistPrimes_stepZero_eq_top h I.mu0 c'.1]
      intro P _
      trivial⟩)
  let st : (I.stp u I.mu0 0).Stab c' := ⟨t, by
    show _ = _
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hsd ?_)) ?_)
    · funext P
      show s.1.1.1 * p0.1.1.1.2 P * (⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩⁻¹ : ↥(GLint B.fields.E (B.R.N 0) P.1)).1 = p0.1.1.1.2 P
      simp only [Subgroup.coe_inv]
      group
    · show (fun v => s.1.1.1 v) '' p0.1.2 = p0.1.2
      rw [idx_empty I.mu0 u p0, Set.image_empty]⟩
  have hsub := (Nat.card_eq_one_iff_unique.1 (hm c')).1
  have e : st = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : (I.stp u I.mu0 0).Stab c' => x.1.1) e

theorem card_stab_zero (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1) (c : (I.stp u a 0).Cl) :
    Nat.card ((I.stp u a 0).Stab c) = 1 := by
  have e : ∀ s : (I.stp u a 0).Stab c, s = 1 := fun s =>
    Subtype.ext (((l.ch u a).step 0).stab_inj c.1 s.1 _ s.2 (by
      change (ufGL _ _) s.1.1 = 1
      rw [gam_eq_one h u a hm c s, map_one]))
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun s s' => (e s).trans (e s').symm⟩, ⟨1⟩⟩

end GlobalTheory.Pdv.StabZero

namespace GlobalTheory.Pdv

open GlobalTheory.Pdv.StabZero

theorem stepZero_trivial_stabilisers_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  intro B X I h _ l Z lev
  exact ⟨Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev,
    fun u μ _ c => card_stab_zero h l u μ (fun c' => Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev u c') c⟩

end GlobalTheory.Pdv

end
