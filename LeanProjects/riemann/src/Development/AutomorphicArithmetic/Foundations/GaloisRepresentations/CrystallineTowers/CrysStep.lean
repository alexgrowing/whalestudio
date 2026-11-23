import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC TensorProduct
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst CrystallineSemistableComparison UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.Seam

private theorem mat_mul' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ) {a : ℕ}
    (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (σ σ' : K.fixingSubgroup) :
    M.mat n b (σ * σ') = M.mat n b σ * M.mat n b σ' := by
  have h : M.act n (σ * σ') = M.act n σ * M.act n σ' := by
    simp only [Model.act, map_mul]
    rfl
  rw [Model.mat, h, LinearMap.toMatrix_mul]
  rfl

private theorem mat_one' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ) {a : ℕ}
    (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) : M.mat n b 1 = 1 := by
  have h : M.act n 1 = 1 := by
    simp only [Model.act, map_one]
    rfl
  rw [Model.mat, h, LinearMap.toMatrix_one]

theorem UpperTheory.Gal.Seam.crysStep :
    CrystallineSemistableComparison.SmoothModelCrystalline → NiceBc → LocTower → BcCover → IntMap → GoodOf → MatIn → SubAdm → GrCrys → UpperTheory.Gal.Int.Geo.CrysStep := by
  intro hCS hNB hLT hBC hIM hGO hMI hSA hGC E Ω _ _ _ _ _ l _ H θ hN dd ρ hc hp w hw C hOn P AI hT A hA O _ _ _ Bw hj
  obtain ⟨ρ₀, hM, hG⟩ := hp
  obtain ⟨φ, hφ, -⟩ := hIM E Ω l w A hA O Bw hj
  haveI := Bw.Kw.2
  have hN' := hNB E _ (kOf Bw) H hN
  obtain ⟨ρ₁, hM₁, hρ⟩ := hLT l E ↥Bw.Kw.1 Ω (PadicAlgCl l) (kOf Bw) Bw.j (fun _ => rfl) H hN (Om l) θ dd ρ₀ hM
  obtain ⟨C', u, -, -, hOn', -, -⟩ := hBC E ↥Bw.Kw.1 (Ow w) ↥(OK l Bw.Kw.1) (Om l) (kOf Bw) φ hφ H θ C
  obtain ⟨N, a, b, M, hinj, hmat⟩ := hMI l Bw.Kw (bcAlong H (kOf Bw)) θ hN' C' (hOn' hOn) dd ρ₁ hM₁
  obtain ⟨FreeQuotientRank⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  have hgood : (mod C').Good := hGO l Bw.Kw.1 (mod C') C'.smooth C'.proj
  have hcr : IsCrysAt P Bw (ρ₀.comp (Dec (F := E) A).subtype) := by
    refine hSA l P AI hT E Ω (Dec (F := E) A) O Bw N dd a (fun n => (mod C').mat n (b n)) _ (fun n => ⟨mat_one' _ _ _, mat_mul' _ _ _, ?_⟩) M hinj ?_
    · exact isAdmP_of_isAdm FreeQuotientRank (hCS l Bw.Kw.1 (mod C') hgood C'.smooth n (a n) (b n))
    · intro g
      have := hmat (Bw.e g)
      rw [this]
      congr 2
      exact hρ _ _ fun x => Bw.e_comm g x
  obtain ⟨c, hc'⟩ := hG
  exact hGC l P AI hT E Ω _ O Bw dd _ _ ⟨c, fun g => hc' g⟩ hcr
