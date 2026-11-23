import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ac_map {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}
    (φ : R →+* S) (hφ : I ≤ J.comap φ) {f : Γ → R} (hf : AdicCont I f) : AdicCont J fun g => φ (f g) := by
  intro N
  have hN : I ^ N ≤ (J ^ N).comap φ := (Ideal.pow_right_mono hφ N).trans (Ideal.le_comap_pow φ N)
  exact (hf N).comp (Ideal.quotientMap (J ^ N) φ hN)

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  have h := IsLocallyConstant.comp₂ (hf N) (hg N) (· * ·)
  convert h using 1
  funext x
  simp [map_mul]

private theorem ac_comp {Γ Γ' R : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) {u : Γ' → Γ} (hu : Continuous u) : AdicCont I fun x => f (u x) :=
  fun N => (hf N).comp_continuous hu

theorem UpperTheory.V.Ws.P1.redPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (k : Type) [Field k] [Algebra (ResidueField c'.O) k] [Algebra c'.O k] [IsScalarTower c'.O (ResidueField c'.O) k] (Q : PD T.ι (G T.F Ω) (PowerSeries k)), T.PsPair h k Q → ∀ ψ : ∀ v : K.V.frame.Vl, Fin 4 → K.V.frame.Gv v →* (PowerSeries k)ˣ, K.IsPsi ψ Q →
          (∀ v i, W.pushCh (PowerSeries.constantCoeff : PowerSeries k →+* k) (ψ v i) = W.pushCh (algebraMap (ResidueField c'.O) k) (K.r.psib v i)) ∧
          ∀ v i, AdicCont (maximalIdeal (PowerSeries k)) fun g => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k) := by
  intro Ω _ _ _ l _ c D T c' h K k _ _ _ _ Q hQ ψ hψ
  obtain ⟨-, -, hcont, -, hres, hdec⟩ := P1.towerGal D T
  have hc : ∀ a : c'.O, PowerSeries.constantCoeff (algebraMap c'.O (PowerSeries k) a) = algebraMap c'.O k a := by
    intro a
    first
      | rfl
      | simp
  constructor
  · intro v i
    ext g
    simp only [W.pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    rw [hψ v i g, map_mul, K.psib v i g, K.chib i]
    obtain ⟨g, hg0⟩ := (show ↥(Dec (K.s.A ↑(show W.Vl l T.L from v))) from g)
    have hg : (resLe T.F_le) g ∈ Dec (T.pl (K.e v)) := by
      rw [← K.hA v]
      exact (hdec _ _).1.2 hg0
    rw [hQ.psi _ _ _ hg, (hres g).1, hc, map_mul (residue _), map_mul,
      ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  · intro v i
    have hφ : maximalIdeal c'.O ≤ (maximalIdeal (PowerSeries k)).comap (algebraMap c'.O (PowerSeries k)) := by
      intro a ha
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, hc, hQ.loc a ha]
      exact not_isUnit_zero
    have h1 : AdicCont (maximalIdeal (PowerSeries k))
        (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => algebraMap c'.O (PowerSeries k) ↑(K.κ g.1)) :=
      ac_comp (ac_map _ hφ K.κ_cont) continuous_subtype_val
    have h2 : AdicCont (maximalIdeal (PowerSeries k))
        (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => Q.ψ (K.e v) i (resLe T.F_le g.1)) := by
      have := (sxAdicMat _ _ hQ.cont).2 (adj (Q.n (K.e v))) (Q.n (K.e v)) i i
      exact ac_comp this (hcont.comp continuous_subtype_val)
    have key := ac_mul h1 h2
    have e : (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k)) =
        fun g => algebraMap c'.O (PowerSeries k) ↑(K.κ g.1) * Q.ψ (K.e v) i (resLe T.F_le g.1) :=
      funext fun g => hψ v i g
    show AdicCont _ (fun g : Dec (K.s.A ↑(show W.Vl l T.L from v)) => ((ψ v i g : (PowerSeries k)ˣ) : PowerSeries k))
    rw [e]
    exact key
