import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRel

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc

namespace UpperTheory.Esk.HyperbolicIntegrabilityLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pInf_alg (v : InfinitePlace F) (x : F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  have e : TR.pInf F (algebraMap F (Ad F) x) v = (v.embedding x).re := by
    rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
    simp
  rw [e, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

omit [IsTotallyReal F] in
theorem fin_zc (u : (Af F)ˣ) : finGL F 2 (zc F u) = Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F u) := by
  rw [zc, finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  rfl

def rr (γ : GL (Fin 2) F) : GL (Fin 2) (TR.Rinf F) := Matrix.GeneralLinearGroup.map ((TR.pInf F).comp (algebraMap F (Ad F))) γ

theorem gv_rr (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (γ : GL (Fin 2) F) (v : InfinitePlace F) : gv v (rr γ) = (mkDat c χ).r v γ :=
  Units.ext (Matrix.ext fun i j => pInf_alg v (γ i j))

theorem rat_eq (γ : GL (Fin 2) F) : ratGL F 2 γ = TR.infGL F 2 (rr γ) * finGL F 2 (jF F γ) := by
  rw [← TR.infGL_mul_finGL (ratGL F 2 γ)]
  rfl

omit [IsTotallyReal F] in
theorem sc_comm (s : Ideles F) (a : GA F 2) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s * a = a * Matrix.GeneralLinearGroup.scalar (Fin 2) s :=
  Units.ext (Matrix.scalar_commute (s : Ad F) (fun _ => Commute.all _ _) a.val).eq

theorem aut (hb : B1b) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (χ : Hc c →* ℂˣ) (φ : TR.Sm F 2) (hφ : TR.IsAutForm φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (γ : GL (Fin 2) F) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    f ((mkDat c χ).act γ (fun v => gv v g • iP), jF F γ * x) =
      (mkDat c χ).J k γ (fun v => gv v g • iP) * f ((fun v => gv v g • iP), x) := by
  have e1 : (mkDat c χ).act γ (fun v => gv v g • iP) = fun v => gv v (rr γ * g) • iP := funext fun v => by
    change (mkDat c χ).r v γ • gv v g • iP = _
    rw [map_mul, mul_smul, gv_rr c χ]
  have e4 : TR.infGL F 2 (rr γ * g) * finGL F 2 (jF F γ * x) = ratGL F 2 γ * (TR.infGL F 2 g * finGL F 2 x) := by
    rw [rat_eq, map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (TR.infGL F 2 g), TR.infGL_comm, mul_assoc]
  have e5 : ∀ v, j1 (k v) (gv v (rr γ * g)) iP = j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP) * j1 (k v) (gv v g) iP :=
    fun v => by rw [map_mul, hb.1, gv_rr c χ]
  rw [e1, ← hf, ← hf, e4, hφ.left, Finset.prod_congr rfl fun v _ => e5 v, Finset.prod_mul_distrib]
  change _ = (∏ v, j1 (k v) ((mkDat c χ).r v γ) (gv v g • iP)) * _
  ring

theorem lev (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F) (χ : Hc c →* ℂˣ) (hχ : IsChi c ω χ) (φ : TR.Sm F 2)
    (hcent : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g)
    (hfix : ∀ u ∈ Kc c, TR.finRep F 2 u φ = φ)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) (h : Hc c) :
    f ((fun v => gv v g • iP), x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f ((fun v => gv v g • iP), x) := by
  obtain ⟨⟨κ, hκ, z0, hz⟩, hv⟩ := hχ h
  have e5 : φ.1 (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) = φ.1 (TR.infGL F 2 g * finGL F 2 x) :=
    congrArg (fun ψ : TR.Sm F 2 => ψ.1 (TR.infGL F 2 g * finGL F 2 x)) (hfix κ hκ)
  have e6 : TR.infGL F 2 g * finGL F 2 (x * (h : GF F)) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (finId F z0) * (TR.infGL F 2 g * finGL F 2 x * finGL F 2 κ) := by
    rw [hz, map_mul, map_mul, fin_zc, sc_comm]
    simp only [mul_assoc]
  rw [← hf, ← hf, hv κ hκ z0 hz, e6, hcent, e5, mul_assoc]

theorem bdd (hb : B1b) (k : InfinitePlace F → ℕ) (φ : TR.Sm F 2) (C : ℝ) (hC : ∀ g, ‖φ.1 g‖ ≤ C)
    (f : X (InfinitePlace F) × GF F → ℂ) (hf : Rel k f φ.1) (g : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    ‖f ((fun v => gv v g • iP), x)‖ * nrm k (fun v => gv v g • iP) ≤ C := by
  have e : ∀ v, ‖j1 (k v) (gv v g) iP‖ * |(gv v g • iP).1.im| ^ ((k v : ℝ) / 2) = 1 := fun v => by
    rw [hb.2.2.2.2.1]
    simp [iP]
  rw [← hf g x, norm_mul, nrm, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
  simp only [e, Finset.prod_const_one, mul_one]
  exact hC _

end UpperTheory.Esk.HyperbolicIntegrabilityLemmas

open UpperTheory.Esk in
theorem UpperTheory.Esk.hyperbolic_terms_integrable_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H0 → UpperTheory.Esk.H1a → UpperTheory.Esk.H1b → UpperTheory.Esk.H1c → UpperTheory.Esk.H1 := by
  intro hb hc h0 h1a h1b h1c F _ _ _ k c ω χ hω hχ φ hφ hcusp
  obtain ⟨f, hf⟩ := h1a F k c ω φ hω hφ
  refine ⟨f, ⟨h1b F k c ω φ hω hφ f hf, fun γ z x => ?_, fun z x h => ?_, ?_⟩, hf⟩
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.aut hb k c χ φ hφ.aut f hf γ g x
  · obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    by_cases h0φ : φ = 0
    · have e : ∀ g x, f (fun v => gv v g • iP, x) = 0 := fun g x => by rw [← hf g x, h0φ]; simp
      change f (_, x * (h : GF F)) = ((χ h : ℂˣ) : ℂ) * f (_, x)
      rw [e, e, mul_zero]
    obtain ⟨-, hfix, -⟩ := h0 F k c ω φ hφ h0φ
    exact HyperbolicIntegrabilityLemmas.lev k c ω χ hχ φ hφ.cent hfix f hf g x h
  · obtain ⟨C, hC⟩ := h1c F k c ω φ hω hφ hcusp
    refine ⟨C, fun z x => ?_⟩
    obtain ⟨g, rfl⟩ := HeckeRelationLemmas.exists_g hc z
    exact HyperbolicIntegrabilityLemmas.bdd hb k φ C hC f hf g x
