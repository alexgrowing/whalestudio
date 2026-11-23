import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hc : IsCompact (U : Set G)) (ho : IsOpen (U : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨U, hc⟩, by
    rw [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]
    exact ⟨1, U.one_mem⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem poly_mem {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    polyEmb n (aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) p) ∈ symmetricLaurent n := fun σ => by
  rw [← polyEmb_rename]
  congr 1
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  exact MvPolynomial.esymm_isSymmetric (Fin n) ℂ _ σ

theorem UpperTheory.ConvolutionTheory.GM.sphEx :
    SphEx := by
  intro K _ _ n _ w
  refine ⟨fun p => ?_, ?_, ?_⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    obtain ⟨H, hH⟩ := (AlgHom.mem_range _).1 (symmetricLaurent_le_range (μ := m) (F := w.adicCompletion K) (poly_mem p))
    exact ⟨fun x => (H : HeckeAlgebra m) x, _, inferInstance, m, hm, h1, H, fun _ => rfl, hH⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    refine ⟨_, inferInstance, m, hm, h1, 1, fun x => ?_, by rw [map_one, map_one, map_one]⟩
    rw [HeckeAlgebra.HeckeAlgebraLevel.val_one]
    have hr : m.real (GLnLocal.integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1 := by
      simp [Measure.real, h1]
    rw [HeckeAlgebra.idem_apply, hr]
    simp only [Complex.ofReal_one, inv_one]
    rfl
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1, (H : HeckeAlgebra m).mem.2,
      fun k hk x => HeckeAlgebra.HeckeAlgebraLevel.val_mem _ _ H k hk x⟩
