import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelSmallK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldDefs

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
theorem smallS_of_k (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hF : SliceFacts) (hU : SubSplit) (hH : HaarLc) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k := by
  intro hT F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop hTf
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hcm : IsCMExt F E σ := d.ok.good.cm
  have hJ : d.A.J.det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact (GlobalTheory.T.isUnit_det_gram_of_hermitianSelfDualLatticeSpace F E σ d.B d.m d.A d.r d.s hA).ne_zero
    · exact (GlobalTheory.T.isUnit_det_gram_skewHermitian_signature F E σ d.B d.m d.A d.r d.s hA).ne_zero
  obtain ⟨hc1, -, -, -, hc5⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  have hlin := d.ok.dbl.lin
  have pres1 : ∀ u : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S u ∘ₗ S1') φ ∈ schA F (K1 d.m n) :=
    fun u φ hφ => hop.pres _ (hlin.pres u _ (hop.pres' φ hφ))
  have one1 : ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S 1 ∘ₗ S1') φ = φ := fun φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_one, Module.End.one_apply]
    exact hop.right φ hφ
  have mul1 : ∀ u v : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n),
      (S1 ∘ₗ d.S (u * v) ∘ₗ S1') φ = (S1 ∘ₗ d.S u ∘ₗ S1') ((S1 ∘ₗ d.S v ∘ₗ S1') φ) := fun u v φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_mul, Module.End.mul_apply]
    rw [hop.left _ (hlin.pres v _ (hop.pres' φ hφ))]
  obtain ⟨SA1, hSA1⟩ := projHom (fun u => S1 ∘ₗ d.S u ∘ₗ S1') pres1 one1 mul1
  have hsplit : IsUSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm)
      (fun (g : UA σ d.A.J) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) => mat g * x) SA1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop hSA1 hlin
  have hexp : ∀ u : UA σ d.A.J, ∀ Ψ ∈ schA F (K1 d.m n), ∀ x : K1 d.m n → AF F,
      SA1 u Ψ x = Ψ (Sum.elim (Lk d.bs (mat u⁻¹) (x ∘ Sum.inl)) (Lc d.bs (mat u⁻¹) (x ∘ Sum.inr))) := by
    intro u Ψ hΨ x
    set X : Mx F E d.m d.n := cmbB d.bs (x ∘ (eK d.m h).symm) with hX
    have hx : crdB d.bs X ∘ eK d.m h = x := by
      rw [hX, crdB_cmbB]; funext k; simp
    have hΦ : S1' Ψ ∈ d.sch := hop.pres' Ψ hΨ
    have hTP := (hT.2.1 F E σ d (S1' Ψ) hΦ).2.2 u X
    rw [hTf _ (hlin.pres u _ hΦ), hTf _ hΦ, hop.right Ψ hΨ] at hTP
    have key := mul_left_cancel₀ hC0 hTP
    calc SA1 u Ψ x = S1 (d.S u (S1' Ψ)) x := by rw [hSA1 u Ψ hΨ]; rfl
      _ = S1 (d.S u (S1' Ψ)) (crdB d.bs X ∘ eK d.m h) := by rw [hx]
      _ = Ψ (crdB d.bs (mat u⁻¹ * X) ∘ eK d.m h) := key
      _ = _ := by rw [← Lk_crdB, hX, crdB_cmbB, Lk_eK]
  have hbox : ∀ u : UA σ d.A.J, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), ∀ φ'' ∈ schA F (Fin d.m × Fin 2),
      SA1 u (boxFun φ' φ'') = boxFun (φ' ∘ Lk d.bs (mat u⁻¹)) (φ'' ∘ Lc d.bs (mat u⁻¹)) := by
    intro u φ' h' φ'' h''
    funext x
    rw [hexp u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' h' φ'' h'')]
    rfl
  obtain ⟨φ₀, hφ₀, hφ₀1, hφ₀n⟩ := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).2.2.1
  obtain ⟨φa, hφa, hφa1, -⟩ := (hF F (Fin d.m × Fin 2) (Fin d.m × Fin n × Fin 2)).2.2.1
  let c : UA σ d.A.J → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun u => LinearMap.funLeft ℂ ℂ (Lk d.bs (mat u⁻¹))
  have hc : ∀ u φ, c u φ = φ ∘ Lk d.bs (mat u⁻¹) := fun _ _ => rfl
  have presS : ∀ u, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c u φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    intro u φ hφ
    have := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).1 _
      (hsplit.pres u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀))
    rw [hbox u φ hφ φ₀ hφ₀, slice0_box, Function.comp_apply, Lc_zero, hφ₀1, one_smul] at this
    exact this
  have oneS : ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c 1 φ = φ := by
    intro φ _
    have hm : mat (1 : UA σ d.A.J)⁻¹ = 1 := by rw [inv_one]; rfl
    rw [hc, hm]
    funext x
    simp only [Function.comp_apply, Lk_one]
  have mulS : ∀ u v, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c (u * v) φ = c u (c v φ) := by
    intro u v φ _
    rw [hc, hc, hc, mul_inv_rev, show mat (v⁻¹ * u⁻¹) = mat v⁻¹ * mat u⁻¹ from rfl]
    funext x
    simp only [Function.comp_apply, Lk_mul]
  obtain ⟨S', hS'⟩ := projHom c presS oneS mulS
  have hφ₁ : ∀ g : UA σ d.A.J, φ₀ ∘ Lc d.bs (mat g⁻¹) ∈ schA F (Fin d.m × Fin 2) := by
    intro g
    have := sliceL_mem hF (hsplit.pres g _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φa hφa φ₀ hφ₀))
    rw [hbox g φa hφa φ₀ hφ₀] at this
    convert this using 1
    funext x''
    simp only [boxFun, Function.comp_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Lk_zero, hφa1, one_mul]
  have hsplitS : IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' :=
    hU F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2) (Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
      (Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)) _ _ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) dd' (emb h b d.b) hc1
      (UA σ d.A.J) (UA σ d.A.J) (fun g x => mat g * x) (fun g x => mat g * x) (MonoidHom.id _) continuous_id
      (fun g w' => hc5 g w') SA1 S' hsplit φ₀ hφ₀ hφ₀1 hφ₀n (fun g => ⟨φ₀ ∘ Lc d.bs (mat g⁻¹), hφ₁ g,
        by rw [Function.comp_apply, Lc_zero, hφ₀1],
        fun μ'' hμ'' => hH F E σ hcm d.m d.A.J hJ d.bs g⁻¹ μ'' hμ'' (fun x => ‖φ₀ x‖ₑ ^ 2),
        fun φ' hφ' => by
          show SA1 g (boxFun φ' φ₀) = _
          rw [hbox g φ' hφ' φ₀ hφ₀, hS' g φ' hφ', hc]⟩)
  refine ⟨S', hsplitS, fun g Φ hΦ => ?_⟩
  show S' g Φ 0 = Φ 0
  rw [hS' g Φ hΦ, hc, Function.comp_apply, Lk_zero]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
