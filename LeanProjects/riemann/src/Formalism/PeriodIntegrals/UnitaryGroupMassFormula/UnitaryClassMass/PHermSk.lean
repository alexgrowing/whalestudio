import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjS
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryApproxFin

open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def Sw (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : HeightOneSpectrum (𝓞 F)) : Submonoid (𝓞 E) :=
  t.asIdeal.primeCompl.map (algebraMap (𝓞 F) (𝓞 E))

def LocSw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), (∀ a, σ a = star a) → (∀ e, σ e = e → ∃ c : F, algebraMap F E c = e) →
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 E) V] (p : Ideal (𝓞 E)), p.IsMaximal →
    ∀ t : HeightOneSpectrum (𝓞 F), t.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E)) →
    ∀ X : Submodule (𝓞 E) V, loc (K := E) p X = locS (Sw F E t) X

def CloseLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ t : HeightOneSpectrum (𝓞 F),
      (∀ i j, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E)
          (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((g : Matrix (Fin M) (Fin M) E) i j) -
            PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((γ : Matrix (Fin M) (Fin M) E) i j) =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (D' : F)) * s) →
      locS (Sw F E t) (gmap (linOf b γ) L0) = locS (Sw F E t) (gmap (linOf b g) L0)

def WPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : Ideal (𝓞 E)), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥

def BcU : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E),
    g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    Units.map ((PI.UnitaryApproxDefs.inclE (F := F) (E := E) R).mapMatrix :
      Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[F] R)).toMonoidHom g ∈ PI.UnitaryApproxDefs.UPts σ J R

def GramOK : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [StarRing E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ a, σ a = star a) → ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V),
    h.IsSymm → h.Nondegenerate → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) (gramOf h b) ∧ IsUnit (gramOf h b).det

abbrev Fix {E : Type} [Field E] (s : E →+* E) : Subfield E := RingHom.eqLocusField s (RingHom.id E)

def sigFix {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    E →ₐ[Fix (σ : E →+* E)] E :=
  { (σ : E →+* E) with commutes' := fun r => r.2 }

theorem hermApprox_of (hL : LocSw) (hC : CloseLoc) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hS hN hL0 N hNg P hP
  classical
  have hσσ : ∀ e, σ (σ e) = e := fun e => by rw [hσ, hσ, star_star]
  obtain ⟨hH, hdet⟩ := hG F E σ hσ V h M b hS hN
  set J := gramOf h b with hJ
  let K0 : Subfield E := Fix (σ : E →+* E)
  let σ0 : E →ₐ[K0] E := sigFix σ
  have hσ0 : ∀ e, σ0 e = σ e := fun _ => rfl
  have hσσ0 : ∀ e, σ0 (σ0 e) = e := fun e => hσσ e
  have hθ0 : ∃ θ, σ0 θ ≠ θ := hθ
  have hH0 : PI.UnitaryApproxDefs.IsHerm (σ0 : E →+* E) J := hH
  have hfix : ∀ e, σ0 e = e → ∃ c : K0, algebraMap K0 E c = e := fun e he => ⟨⟨e, he⟩, rfl⟩
  have hσstar : ∀ a, σ0 a = star a := fun a => hσ a

  have wit : ∀ p : P, ∃ u ∈ isom h,
      gmap u (loc (K := E) (p : Ideal (𝓞 E)) L0) = loc (K := E) (p : Ideal (𝓞 E)) N :=
    fun p => hNg.2 p (hP p p.2)
  choose u hu hul using wit
  let g : P → GL (Fin M) E := fun p => matGL b (u p)
  have hg : ∀ p, g p ∈ PI.UnitaryApproxDefs.UJ (σ0 : E →+* E) J := fun p => matGL_mem σ hσ h b (hu p)

  let w : P → HeightOneSpectrum (𝓞 K0) := fun p =>
    ⟨(p : Ideal (𝓞 E)).comap (algebraMap (𝓞 K0) (𝓞 E)),
      by have := (hP _ p.2).isPrime; infer_instance, hW K0 E _ (hP _ p.2)⟩
  let T : Finset (HeightOneSpectrum (𝓞 K0)) := Finset.univ.image w
  let gl : (t : HeightOneSpectrum (𝓞 K0)) → GL (Fin M) (E ⊗[K0] t.adicCompletion K0) := fun t =>
    if hx : ∃ p, w p = t then
      Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) (t.adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] t.adicCompletion K0)).toMonoidHom
          (g (Classical.choose hx))
    else 1
  have hgl : ∀ t ∈ T, gl t ∈ PI.UnitaryApproxDefs.UPts σ0 J (t.adicCompletion K0) := by
    intro t _
    by_cases hx : ∃ p, w p = t
    · simp only [gl, dif_pos hx]
      exact hB K0 E σ0 M J _ _ (hg _)
    · simp only [gl, dif_neg hx]
      exact one_mem _

  have hCp := fun p : P => hC K0 E σ0 V M J b L0 hσσ0 hH0 hdet hL0 (g p) (hg p)
  choose D hD0 hDcl using hCp
  let Dall : 𝓞 K0 := ∏ p, D p
  have hDall : Dall ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 p
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite K0 E (Fin M) σ0 J hσσ0 hθ0 hH0 hdet
    T gl hgl Dall hDall
  refine ⟨⟨γ, hγ⟩, fun q hq => ?_⟩
  let q' : P := ⟨q, hq⟩
  have hx : ∃ p, w p = w q' := ⟨q', rfl⟩
  set ps := Classical.choose hx with hps
  have hpw : w ps = w q' := Classical.choose_spec hx
  have hT : w q' ∈ T := Finset.mem_image_of_mem w (Finset.mem_univ _)
  have hcong := hc (w q') hT
  have hglq : gl (w q') = Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) ((w q').adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] (w q').adicCompletion K0)).toMonoidHom
          (g ps) := dif_pos hx
  rw [hglq] at hcong
  have hcl := hDcl ps Dall (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) γ hγ (w q') hcong
  have eq1 := hL K0 E σ0 hσstar hfix V q (hP q hq) (w q') rfl
  have eq2 := hL K0 E σ0 hσstar hfix V (ps : Ideal (𝓞 E)) (hP _ ps.2) (w q') (by rw [← hpw])
  show loc (K := E) q (gmap (linOf b γ) L0) = loc (K := E) q N
  rw [eq1, eq1, hcl, ← eq2, ← eq2, linOf_matGL, locGmapStep E V (u ps) (ps : Ideal (𝓞 E)) L0]
  exact hul ps

end PI.UnitaryGroupMassFormula.UJClassMass

end
