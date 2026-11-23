import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.ComapLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapStar

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.resid_desc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (g : G.Hom G') (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G.frame O n), (∀ a : G.G₀, g.p₀ a = 1 → ∀ i, r.chib i a = 1) → ∃ r' : Resid G'.frame O n, Glob.Compat g r r' ∧ ((∀ w, r.Ip w = G.frame.Iu w) → ∀ w, r'.Ip w = G'.frame.Iu w) := by
  intro l _ L G G' g n O _ _ _ r hker
  let c : Fin n → G'.frame.G₀ →* (ResidueField O)ˣ := fun i =>
    g.p₀.liftOfSurjective g.p₀_surj ⟨r.chib i, fun a ha => by
      rw [MonoidHom.mem_ker] at ha ⊢
      exact hker a ha i⟩
  have hca : ∀ i a, c i (g.p₀ a) = r.chib i a := fun i a =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hc : ∀ i, (c i).comp g.p₀ = r.chib i := fun i => by
    ext a
    simp only [MonoidHom.comp_apply, hca]
  have hdiag : (diagRep c).comp g.p₀ = diagRep r.chib := by
    ext a
    simp only [MonoidHom.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk, hca]
  have hD : (GDet.ofRep (diagRep c)).comap g.p₀ = GDet.ofRep (diagRep r.chib) := by
    rw [(comap_lam n (ResidueField O) _ _ g.p₀ (GDet.ofRep (diagRep c))).2.2.2.2.1 (diagRep c), hdiag]
  have key : ∀ (B : Type) [CommRing B] [Algebra (ResidueField O) B] (z : MonoidAlgebra B G.frame.G₀),
      (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z) =
        (GDet.ofRep (diagRep r.chib)).D B z := by
    intro B _ _ z
    calc (GDet.ofRep (diagRep c)).D B (MonoidAlgebra.mapDomainRingHom B g.p₀ z)
        = ((GDet.ofRep (diagRep c)).comap g.p₀).D B z := rfl
      _ = (GDet.ofRep (diagRep r.chib)).D B z := by rw [hD]
  let r' : Resid G'.frame O n :=
    { chib := c
      chib_open := fun i => by
        rw [← g.p₀_quot.isOpen_preimage]
        have hset : (g.p₀ ⁻¹' ((c i).ker : Set G'.frame.G₀)) = ((r.chib i).ker : Set G.frame.G₀) := by
          ext a
          simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, hca]
        rw [hset]
        exact r.chib_open i
      chib_inj := fun i j hij => by
        apply r.chib_inj
        rw [← hc i, ← hc j, hij]
      polar := by
        intro B _ _ _ _ y
        obtain ⟨x0, hx0⟩ := Finsupp.mapDomain_surjective (M := B) g.p₀_surj y.coeff
        have hx' : MonoidAlgebra.mapDomainRingHom B g.p₀ (MonoidAlgebra.ofCoeff x0) = y := by
          rw [MonoidAlgebra.mapDomainRingHom_apply]
          show MonoidAlgebra.ofCoeff (Finsupp.mapDomain _ x0) = y
          rw [hx0]
        rw [← hx', ← (map_star l L G G' g n O B).1 (MonoidAlgebra.ofCoeff x0), key, key]
        exact r.polar B _
      psib := r.psib
      psib_open := r.psib_open
      th := r.th
      th_comm := r.th_comm }
  refine ⟨r', ⟨fun i => (hc i).symm, rfl, rfl⟩, ?_⟩
  intro hIp w
  have hle : ∀ i, G.frame.Iu w ≤ (r.chib i).ker := by
    intro i
    have h1 := hIp w
    unfold Resid.Ip at h1
    exact (inf_eq_left.mp h1).trans (iInf_le _ i)
  unfold Resid.Ip
  apply inf_eq_left.mpr
  rw [le_iInf_iff]
  intro i
  rintro _ ⟨x, hx, rfl⟩
  show c i ((G'.φu w) x) = 1
  rw [← g.p₀_φu w x, hca]
  exact hle i ⟨x, hx, rfl⟩
