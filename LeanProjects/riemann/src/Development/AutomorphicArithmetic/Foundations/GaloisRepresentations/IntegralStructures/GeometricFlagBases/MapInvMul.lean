import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open GlobalTheory.GalV (HTower)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (algSat tw)
open UpperTheory.Gal.TP.Sub (Cl unrPol)
open UpperTheory.Gal.crystallineComparison (heckePol rootPol)
open UpperTheory.Gal.Int.Div (CrysAt PhiKilled HTRichEx JumpsOcc VBase)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo

structure Steps : Prop where
  rep : RepEx
  es : ESStep
  crys : CrysStep
  jump : JumpStep
  phi : PhiStep
  cut : CutStep
  twES : TwES
  twCrys : TwCrys
  twJ : TwJ
  twPhi : TwPhi
  phiOf : PhiOf
  card : SatCard
  jumpsOf : JumpsOf
  rich : RichOf
  char : TP.Sub.CharEx
  ss : TP.Sub.SSLeft
  cont : TP.Sub.ContLeft

theorem map_inv_mul (R : Multiset ℂ) (c : ℂˣ) : (R.map (· * ((c : ℂ))⁻¹)).map (· * (c : ℂ)) = R := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id R]
  exact Multiset.map_congr rfl fun x _ => by simp

theorem Pack.rep (h : Steps) {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a d : ℕ} {U : Submodule ℂ (UA E a → ℂ)} (P : Pack ι d U)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal) (hlac : LacWtAt ι v U) (hP : P.HTFor v) :
    ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VBase ι d U ρ ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → ESAt ι ρ w (algSat a (normV w) B)) ∧
      (∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w → CrysAt ρ w ∧ JumpsOcc U ι ρ w) ∧
      ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.CongAll w → ∀ B, SatU U w B → PhiKilled ι ρ w a B := by
  obtain ⟨dd, ρ, hc, hs, hp⟩ := h.rep E Ω l P.H P.θ P.nice
  obtain ⟨L, hL, -⟩ := h.char E Ω l ι
  obtain ⟨hχ, hcl⟩ := hL P.κ P.m P.alg
  have hES : ∀ w B, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → CongFor ι a P.H P.θ P.κ w B →
      ESAt ι (tw ρ (L P.κ P.m)) w (algSat a (normV w) B) := by
    rintro w B hw ⟨hu, ϑ, h1, h2⟩
    have := h.twES E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) hw _
      (h.es E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rwa [map_inv_mul] at this
  have hHT : ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → P.HTFor w →
      CrysAt (tw ρ (L P.κ P.m)) w ∧ JumpsOcc U ι (tw ρ (L P.κ P.m)) w := by
    rintro w hw ⟨hu, h1, h2⟩
    have hg := (h.cut E _ P.H P.θ P.nice w).1 h1
    have h3 : ∀ τ : E →+* ℂ, ∃ σ : ℂ ≃+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam → ∀ j ∈ GlobalTheory.RoadWGeo.wtJumps lam,
        HodgeAt (ι.trans σ) P.H P.θ (σ.toRingHom.comp τ) (j + P.m τ) := fun τ => by
      by_cases hτ : OverPl ι τ w
      · obtain ⟨σ, hσ⟩ := h2 τ hτ
        exact ⟨σ, fun _ => hσ⟩
      · exact ⟨RingEquiv.refl ℂ, fun h' => absurd h' hτ⟩
    choose σ hσ using h3
    have hJ : JOcc ι ρ w fun τ j => HodgeAt (ι.trans (σ τ)) P.H P.θ ((σ τ).toRingHom.comp τ) j := by
      intro Q AI hT A hA O _ _ _ Bw hj τ LL' τ' hi
      exact h.jump E Ω l (ι.trans (σ (ι.toRingHom.comp τ))) P.H P.θ P.nice dd ρ hc hp w hw hg Q AI hT A hA O Bw hj τ LL' τ' hi
    refine ⟨?_, h.jumpsOf E Ω l ι a dd U _ w _ ?_ (h.twJ E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _ hJ)⟩
    · obtain ⟨C, hC, -⟩ := hg
      exact h.twCrys E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) (h.crys E Ω l P.H P.θ P.nice dd ρ hc hp w hw C hC)
    · intro τ hτ lam hl j hj
      simpa only [sub_neg_eq_add] using hσ τ hτ lam hl j hj
  refine ⟨dd, tw ρ (L P.κ P.m), ⟨(h.cont _ _ dd 0).2.2.1 ρ _ hc hχ, (h.ss _ _ dd 0).2.2 ρ _ hs, ?_,
    h.rich E Ω l ι a dd U _ v hv hlac (hHT v hv hP).2⟩, fun w hw hC B hB => hES w B hw (hC B hB), hHT, ?_⟩
  · obtain ⟨X, hX⟩ := P.cong
    exact ⟨X, fun w h1 h2 h3 B hB => hES w B h3 (hX w h1 h2 h3 B hB)⟩
  · intro w hw hC B hB
    obtain ⟨hu, ϑ, h1, h2⟩ := hC B hB
    have := h.twPhi E Ω l ι dd ρ _ hc hχ w _ (fun τ => -P.m τ) (hcl w hu) _
      (h.phi E Ω l ι P.H P.θ P.nice dd ρ hc hp w hw a ϑ _ ((h.cut E _ P.H P.θ P.nice w).2 a ϑ h1) h2)
    rw [map_inv_mul] at this
    exact h.phiOf E Ω l ι dd _ w a B (h.card E a U w B hB) this

theorem geoOne_of (h : Steps) (hP : PackEx) : GeoOne := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph hlac
  obtain ⟨⟨P, hP0⟩, hA, hB⟩ := hP E l ι a ha d hd x hx T hT w₀ v' h0 hv hap h1 S U hU hTy hS hsph
  refine ⟨?_, fun w hw hl hs => ?_, fun w hl hk ha0 hav hs => ?_⟩
  · obtain ⟨dd, ρ, hV, -⟩ := P.rep h Ω hv hlac hP0
    exact ⟨dd, ρ, hV⟩
  · obtain ⟨P, h1, h2⟩ := hA w hw hl hs
    obtain ⟨dd, ρ, hV, hE, -⟩ := P.rep h Ω hv hlac h1
    exact ⟨dd, ρ, hV, hE w hl h2⟩
  · obtain ⟨⟨P, h1, h2⟩, P', h1', h2'⟩ := hB w hl hk ha0 hav hs
    obtain ⟨dd, ρ, hV, -, hC, -⟩ := P.rep h Ω hv hlac h1
    obtain ⟨dd', ρ', hV', -, -, hF⟩ := P'.rep h Ω hv hlac h1'
    exact ⟨⟨dd, ρ, hV, hC w hl h2⟩, dd', ρ', hV', hF w hl h2'⟩

end UpperTheory.Gal.Int.Geo

end
