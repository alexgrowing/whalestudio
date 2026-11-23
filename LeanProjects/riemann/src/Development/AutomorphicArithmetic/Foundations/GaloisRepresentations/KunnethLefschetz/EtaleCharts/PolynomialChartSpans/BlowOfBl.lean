import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.LineEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExistsUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DChartEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DCoord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpChart2
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExChart

noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace UpperTheory.Gal.KunnethLefschetz.G

private theorem etale_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (h : φ.Etale) (σ : Type) :
    (MvPolynomial.map φ : MvPolynomial σ A →+* MvPolynomial σ B).Etale := by
  algebraize [φ]
  let := MvPolynomial.algebraMvPolynomial (σ := σ) (R := A) (S := B)
  have hp : Algebra.IsPushout A (MvPolynomial σ A) B (MvPolynomial σ B) := inferInstance
  haveI := hp.symm
  exact RingHom.Etale.isStableUnderBaseChange A B (MvPolynomial σ A) (MvPolynomial σ B) h

private theorem etale_sum {R B C : Type} [CommRing R] [CommRing B] [CommRing C] (φ : R →+* B) (ψ : B →+* C)
    {n d : ℕ} (u : Fin n → B) (t : Fin d → C)
    (hu : (MvPolynomial.eval₂Hom φ u : MvPolynomial (Fin n) R →+* B).Etale)
    (ht : (MvPolynomial.eval₂Hom ψ t : MvPolynomial (Fin d) B →+* C).Etale) :
    (MvPolynomial.eval₂Hom (ψ.comp φ) (Sum.elim (fun k => ψ (u k)) t) :
      MvPolynomial (Fin n ⊕ Fin d) R →+* C).Etale := by
  let e : MvPolynomial (Fin n ⊕ Fin d) R ≃+* MvPolynomial (Fin d) (MvPolynomial (Fin n) R) :=
    ((MvPolynomial.renameEquiv R (Equiv.sumComm (Fin n) (Fin d))).trans
      (MvPolynomial.sumAlgEquiv R (Fin d) (Fin n))).toRingEquiv
  have he : (e : MvPolynomial (Fin n ⊕ Fin d) R →+* MvPolynomial (Fin d) (MvPolynomial (Fin n) R)).Etale :=
    RingHom.Etale.of_bijective (show Function.Bijective e from e.bijective)
  have key : (MvPolynomial.eval₂Hom (ψ.comp φ) (Sum.elim (fun k => ψ (u k)) t) :
      MvPolynomial (Fin n ⊕ Fin d) R →+* C) =
      (MvPolynomial.eval₂Hom ψ t).comp ((MvPolynomial.map (MvPolynomial.eval₂Hom φ u)).comp (e : _ →+* _)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e]
    · rintro (i | j) <;> simp [e]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.stableUnderComposition _ _ he (etale_map _ hu _)) ht

private theorem chart_etale {R : Type} [CommRing R] {Z : Sch R} {d : ℕ} (c : DChart Z d) :
    (MvPolynomial.eval₂Hom (Pb.strV (XX Z).hom c.N) (Sum.elim (fun k => secMap (p1 Z) c.h1 (c.u k)) c.s) :
      MvPolynomial (Fin d ⊕ Fin d) R →+* Γ((XX Z).left, c.N)).Etale := by
  have h := etale_sum (algebraMap R (Sec Z c.U)) (secMap (p1 Z) c.h1).toRingHom c.u c.s c.coord.2
    (dCoord R Z d c)
  have e : ((secMap (p1 Z) c.h1).toRingHom.comp (algebraMap R (Sec Z c.U))) = Pb.strV (XX Z).hom c.N := by
    ext r
    exact (secMap (p1 Z) c.h1).commutes r
  rw [e] at h
  exact h

private theorem ker_app {R : Type} [CommRing R] {X Y : Sch R} (i : Y ⟶ X) (V : X.left.Opens) :
    RingHom.ker (i.left.app V).hom = RingHom.ker (secMap i (le_refl (i.left ⁻¹ᵁ V))).toRingHom := by
  rw [Scheme.Hom.app_eq_appLE]
  rfl

theorem blowOfBl : BlowOfBl := by
  intro R _ _ Z W d _ _ π hπ
  obtain ⟨-, hcl, hoff⟩ := blOff R π hπ
  obtain ⟨L, s, hdiv⟩ := exDiv R d π hπ
  have hloc : ∀ y : W.left, ∃ (V : W.left.Opens) (s : Γ(W.left, V)), y ∈ V ∧ IsAffineOpen V ∧
      s ∈ nonZeroDivisors Γ(W.left, V) ∧ RingHom.ker ((exI π).left.app V).hom = Ideal.span {s} := by
    intro y
    have hy : y ∈ iSup L.U := by rw [L.cov.cov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨L.U j, s j, hj, L.cov.aff j, hdiv.nzd j, (ker_app (exI π) (L.U j)).trans (hdiv.ker j)⟩
  obtain ⟨D, f, f_nat, f_u, f_unit, hsup, het, hσ⟩ := lineEx (exI π).left hloc
  have hex : ∀ z : Z.left, ∃ c : DChart Z d, (dg Z).left z ∈ c.N := by
    intro z
    obtain ⟨U, u, hz, hc⟩ := coordEx R Z d z
    obtain ⟨c, -, -, h⟩ := (dChartEx R Z d).1 U u hc z hz
    exact ⟨c, h⟩
  choose c hc using hex
  haveI : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z => (((dg Z).left ⁻¹ᵁ (c z).N : Z.left.Opens) : Set Z.left))
    (fun z => ((dg Z).left ⁻¹ᵁ (c z).N).isOpen) (fun z _ => Set.mem_iUnion.2 ⟨z, hc z⟩)
  have hb : ∀ α : T, BChart π (c α).N (c α).s := fun α => (blChart R π hπ d (c α)).some
  have hσ' : ∀ (α : T) (k : Fin d), ∃ σ : ((hb α).V k : Scheme.{0}) ⟶ D.Y, σ ≫ D.f = ((hb α).V k).ι ∧
      f σ = ((hb α).V k).topIso.inv.hom (secMap π ((hb α).le k) ((c α).s k)) := by
    intro α k
    obtain ⟨-, -, hk, -⟩ := exChart R π d (c α) (hb α) k
    exact hσ ((hb α).V k) _ ((hb α).aff k) ((hb α).nzd k) ((ker_app (exI π) _).trans hk)
  choose σ σ_f f_σ using hσ'
  have hopen : IsOpen (Set.range (dg Z).left)ᶜ := by
    haveI : IsClosedImmersion (dg Z).left := by
      change IsClosedImmersion (pullback.diagonal Z.hom)
      infer_instance
    exact (IsClosedImmersion.isClosedEmbedding (dg Z).left).isClosed_range.isOpen_compl
  let U : (XX Z).left.Opens := ⟨_, hopen⟩
  have hU : (U : Set (XX Z).left) = (Set.range (dg Z).left)ᶜ := rfl
  obtain ⟨hiso, hpre⟩ := hoff U hU
  refine ⟨D, het, ⟨{
    closed := by
      change IsClosedImmersion (pullback.diagonal Z.hom)
      infer_instance
    f := fun a => f a
    f_nat := f_nat
    f_u := f_u
    U := U
    U_eq := hU
    iso := hiso
    unit := fun {V} a ha => f_unit a fun v hv => by
      have h1 : (a ≫ D.f) v ∈ ((π.left ⁻¹ᵁ U : W.left.Opens) : Set W.left) := by
        have h2 := ha (show v ∈ (⊤ : V.Opens) from trivial)
        simpa using h2
      rw [hpre] at h1
      exact h1 hv
    loc := hsup
    ι := T
    V := fun α => (c α).N
    cover := fun z _ => by
      obtain ⟨w, hw⟩ := Set.mem_iUnion.1 (hT (Set.mem_univ z))
      obtain ⟨hwT, hw⟩ := Set.mem_iUnion.1 hw
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨w, hwT⟩, hw⟩
    c := fun α =>
      { affine := (c α).aff
        n := d
        x := fun k => secMap (p1 Z) (c α).h1 ((c α).u k)
        t := (c α).s
        etale := chart_etale (c α)
        ker := (ker_app (dg Z) (c α).N).trans (c α).ker
        C := (hb α).V
        C_aff := (hb α).aff
        C_le := (hb α).le
        C_cover := (hb α).cov.ge
        u := (hb α).y
        surj := (hb α).surj
        rel := (hb α).ker
        inter := (hb α).inter }
    σ := σ
    σ_f := σ_f
    f_σ := f_σ }⟩⟩

end UpperTheory.Gal.KunnethLefschetz.G
