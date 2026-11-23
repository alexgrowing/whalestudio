import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.CohLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.AnnBc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.GalOut
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FiniteOpenHomsToFiniteGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RmapsEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CharpolyElementEqAevalGroupElement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PiSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.EventuallyExistsPatchedModuleQuotientMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FreeNQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedModuleFreeFiniteOverIwasawaAlgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedModuleAnnihilatorLeComapIffIdealLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LaDimArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.T3Of
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedTraceSingleMulSubOneApproxAnnihilated
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedLamConjTwistApproxAnnihilated
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedTraceLocalCharPolyApproxAnnihilated
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.EventuallyTraceInertiaCongruenceOfAdapted
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.MapRingHomSingleMulCharpolyElement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.MapRingHomSingleMulPartialCharpolyElement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.InjOfProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.NonssT
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChainAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChiRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.DiscStMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaOverLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep

open IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa.Core
open scoped TensorProduct

namespace UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {T : TWGrp G0} {n : ℕ}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O]
    {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
    (A : TWAut u J Unit D T)

private theorem lift_pt (hA : Adapted T (r := r))
    (hadj : Algebra.adjoin B (Set.range fun p : Fin T.q × Fin n => (Sp.u _ _ p.1 p.2 : Spo A)) = ⊤)
    {D0 : ℕ} (x : Pt T u D0) (P : Ideal (Spo A)) (hP : P.IsPrime)
    (h : P.comap (algebraMap B (Spo A)) = RingHom.ker x.f) :
    ∃ x' : Spo A →ₐ[O] x.x.A, (∀ b, x' (algebraMap B (Spo A) b) = x.f b) ∧ RingHom.ker x' = P := by
  obtain ⟨x', h1, h2⟩ := exists_lift_ker_eq B (Spo A) x.x.A x.f.toRingHom _ _
    (fun p : Fin T.q × Fin n => u.D.chi (MonoidAlgebra.single (T.sg p.1) 1)) hadj (fun p => by
      refine ⟨(chiRes l G0.frame n O r B u (T.sg p.1) (A.ut p.1) (A.ut_res p.1)).1, ?_, ?_⟩
      · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          ← (spRoots B T.q n (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) _ p.1).1, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ p.2) (by simp)
      · have e1 := ((CA.d_gmap u.D).2.2.1 x.f.toRingHom (MonoidAlgebra.single (T.sg p.1) 1)).1
        rw [← e1, x.maps.1, MonoidAlgebra.mapRingHom_single, map_one]
        have e2 : (GDet.ofRep (mat x.x.ρ)).chi (MonoidAlgebra.single (T.sg p.1) 1) = (mat x.x.ρ (T.sg p.1)).charpoly := by
          show (GDet.repAlg _ _ _).det = _
          rw [Matrix.charpoly]
          congr 1
          ext i j : 2
          by_cases hij : i = j <;> simp [GDet.repAlg, Matrix.charmatrix_apply, hij, Matrix.one_apply, Matrix.diagonal_apply]
        rw [e2, (x.eig p.1).2]
        exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _) P hP h
  refine ⟨{ x' with commutes' := fun a => ?_ }, fun b => DFunLike.congr_fun h1 b, h2⟩
  rw [IsScalarTower.algebraMap_apply O B (Spo A)]
  exact (DFunLike.congr_fun h1 (algebraMap O B a)).trans (x.f.commutes a)

end

theorem core : Core := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A hl hP hA hgen h x hx e he hq₁ q hq hqle hst
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI : Finite (ResidueField O) := IsCoef.finite (l := l)
  have hn : 1 ≤ n := (x 0).x.a_pos.trans (x 0).x.a_le
  obtain ⟨Λ⟩ := s4 l L G0 T hP
  obtain ⟨W⟩ := rrEx l L G0 T Λ n O r B u J D A
  obtain ⟨m⟩ := rmapsEx l L G0 T Λ n O r B u J D A W hA
  obtain ⟨⟨hco, hfree, hfin, hadj⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hA
  have hker := piKer l L G0 T Λ n O r B u J D A W m hn hA
  have hsurj := piSurj l L G0 T Λ n O r B u J D A W m hA hgen
  let πb : (W.R ⧸ ii W) →ₐ[O] Spo A := Ideal.Quotient.liftₐ (ii W) m.π fun a ha => hker ha
  have hπb : ∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a := fun a => rfl
  haveI : Nontrivial (W.R ⧸ ii W) := πb.toRingHom.domain_nontrivial
  haveI : IsCO O (W.R ⧸ ii W) := co_quot O W.R _ (Ideal.Quotient.mkₐ O (ii W)) Ideal.Quotient.mk_surjective
  obtain ⟨o⟩ := ooPair l L G0 T Λ n O r B u J D A W hn
  haveI : FaithfulSMul B (Spo A) := inferInstance
  obtain ⟨⟨P, E, hPp, hE⟩, hdown⟩ := BC.chain_lift B (Spo A) h (fun i => RingHom.ker (x i).f) e
    (fun i => RingHom.ker_isPrime _) fun i => ⟨(he i).1, (he i).2.2⟩
  choose x' hx'1 hx'2 using fun i => lift_pt A hA hadj (x i) (P i) (hPp i).1 (hPp i).2
  have hpt := fun i => ooPt l L G0 T Λ n O r B u J D A W m o πb hπb hA _ (x i) (x' i) (hx'1 i) (hx i).1 (hx i).2
  obtain ⟨hf1, hf2, hf3, hf4⟩ := patchedModule_free_finite_over_iwasawaAlgebra l L G0 T Λ n O r B u J D A W m hA
  haveI : IsCO O (abelian₂ O Unit D) := co_mvps O O _
  haveI : Finite (ResidueField (abelian₂ O Unit D)) := Finite.of_surjective _ (resMap_bijective O (abelian₂ O Unit D)).2
  have hy0 : ∀ p, m.π (m.s (MvPowerSeries.X p)) = 0 := fun p => by rw [m.π_s]; simp
  obtain ⟨o5⟩ := s5 (abelian₂ O Unit D) W.R (Fin T.q × Fin n) m.s.toRingHom Λ.U (fo W) (ii W) (MN m) (X0 m) Λ.U_le hf3 hf4
    (freeN l L G0 T Λ n O r B u J D A W m) (eventually_exists_patchedModule_quotient_maps l L G0 T Λ n O r B u J D A W m hP hA)
    ⟨A.ex + 1, {a | Rel W a}, rfl, fun a ha => t3Of l L G0 T Λ n O r B u J D A W m a (by
      cases ha with
      | ker h k e => exact patched_trace_single_mul_sub_one_approx_annihilated l L G0 T Λ n O r B u J D A W m hn hA h k e
      | pol i g g' e => exact patched_lam_conj_twist_approx_annihilated l L G0 T Λ n O r B u J D A W m hA i g g' e
      | ord v g ga h e => exact patched_trace_local_charPoly_approx_annihilated l L G0 T Λ n O r B u J D A W m hA v g ga h e
      | ine w g ga h e e' => exact eventually_trace_inertia_congruence_of_adapted l L G0 T Λ n O r B u J D A W m hA w g ga h e e'
      | q1 j ph h e => exact t3Q1 l L G0 T Λ n O r B u J D A W m hA j ph h e
      | q2 j i ph ta h e e' => exact t3Q2 l L G0 T Λ n O r B u J D A W m hA j i ph ta h e e')⟩
    (Fin (h + 1)) (fun i => (P i).comap m.π) (1 + D)
    (fun i => by
      haveI := (hPp i).1
      refine ⟨Ideal.comap_isPrime _ _, fun a ha => ?_, fun hf => (hpt i).1 ?_, fun a => ?_⟩
      · show m.π a ∈ P i
        rw [show m.π a = 0 from hker ha]; exact zero_mem _
      · have : m.π (fo W) ∈ RingHom.ker (x' i) := by rw [hx'2]; exact hf
        exact this
      · show m.π (m.s (MvPowerSeries.X a)) ∈ P i
        rw [hy0]; exact zero_mem _)
    (fun i => by
      obtain ⟨La, j1, j2, j3, h1, h2, h3⟩ := laDim O (x i).x.K D ((x i).f.comp A.b.lam) (hx i).1 (hx i).2
      refine ⟨La, j1, j2, j3, ?_, h2, h3⟩
      convert h1 using 1
      ext a
      show m.π (m.s (MvPowerSeries.C a)) ∈ P i ↔ (x i).f (A.b.lam a) = 0
      rw [m.π_s, ← hx'2, RingHom.mem_ker, hx'1]; simp)
  have hmaps := ooMaps l L G0 T Λ n O r B u J D A W m o πb hπb
  have hSt : ∀ Q : Ideal (Spo A), DiscSt o.p.D (Q.comap πb) ↔ DiscSt u.D (Q.comap (algebraMap B (Spo A))) := fun Q => by
    have h1 := (BC.discSt_map n _ (Spo A) _ o.p.D).1 πb.toRingHom Q
    rw [hmaps.1, (BC.discSt_map n _ (Spo A) _ _).1, (BC.discSt_map n B B _ u.D).2.1 _ _ Λ.h.p₀_surj] at h1
    exact h1.symm
  have hyE : ∀ (Q : Ideal (Spo A)) a, Ideal.Quotient.mk (ii W) (m.s.toRingHom (MvPowerSeries.X a)) ∈ Q.comap πb := fun Q a => by
    show m.π (m.s (MvPowerSeries.X a)) ∈ Q
    rw [hy0]; exact zero_mem _
  obtain ⟨q₁, a1, a2, a3, a4⟩ := hq₁
  obtain ⟨Q₁, b1, b2, b3⟩ := hdown (P 0) q₁ (hPp 0).1 a1 (by rw [(hPp 0).2]; exact a4)
  obtain ⟨Q, c1, c2, c3⟩ := hdown (P (Fin.last h)) q (hPp _).1 hq (by rw [(hPp _).2]; exact hqle)
  have key := chainAbs (abelian₂ O Unit D) W.R (Fin T.q × Fin n) m.s.toRingHom (ii W) _ h _ _ o5 (DiscSt o.p.D)
    (fun i Q => NonSS (ooKer o) (algebraMap _ (o5.B i)) Q)
    (fun i => by
      haveI := (hPp i).1
      refine ⟨Ideal.comap_isPrime _ _, fun a ha => ?_⟩
      show m.π a ∈ P i
      rw [show m.π a = 0 from hker ha]; exact zero_mem _)
    (BC.discSt_map n _ B _ o.p.D).2.2
    (fun i Z Q hZ hQ h1 h2 h3 => by
      obtain ⟨Pt, e1, e2⟩ := (hpt i).2
      obtain ⟨k1, k2, k3⟩ := cohLim l L G0 T Λ n (x i).x (x i).k (x i).al _ hl hP (x i).eig (x i).b1 (x i).b2
      have hc : IsCplAt (W.R ⧸ ii W) (RingHom.ker Pt.f) (o5.B i) := by
        convert o5.cpl i using 1
        ext a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rw [Ideal.mem_quotient_iff_mem (fun b hb => by
          show m.π b ∈ P i
          rw [show m.π b = 0 from hker hb]; exact zero_mem _), e1, ← hx'2]
        rfl
      refine galOut l L Λ.G G0 Λ.h n (x i).x (x i).k O o.r' _ o.p Pt (o5.B i) _ hl hc k1 k2 k3 Z Q hZ hQ
        (((BC.discSt_map n _ _ _ o.p.D).1 _ _).2 h1) ?_ ?_
      · convert h2 using 2
        simp [mul_comm, add_assoc]
      · rw [e2]
        exact h3.imp_left ((BC.discSt_map n _ _ _ o.p.D).1 _ _).2)
    (fun i => (E i).comap πb)
    (fun i => by
      haveI := (hE i).1
      refine ⟨Ideal.comap_isPrime _ _, hyE _, Ideal.comap_mono (f := m.π) (hE i).2.2.1, Ideal.comap_mono (f := m.π) (hE i).2.2.2,
        fun Q hQ hQE => nonssT l L G0 T Λ n O r B u J D A W m o πb hπb hP hA hn _ _ Q (E i) hQ (hE i).1 hQE ?_⟩
      rw [(hE i).2.1]; exact (he i).2.1)
    ⟨Q₁.comap πb, Ideal.comap_isPrime _ _, hyE _, Ideal.comap_mono (f := m.π) b3, (hSt _).2 (b2 ▸ a2),
      (patchedModule_annihilator_le_comap_iff_ideal_le l L G0 T Λ n O r B u J D A W m hsurj Q₁ b1).2 (b2 ▸ a3)⟩
    (Q.comap πb) (Ideal.comap_isPrime _ _) (hyE _) (Ideal.comap_mono (f := m.π) c3)
    (hst.imp (fun h1 => (hSt _).2 (c2 ▸ h1)) fun h1 Q' hQ' e =>
      nonssT l L G0 T Λ n O r B u J D A W m o πb hπb hP hA hn _ _ Q' Q hQ' c1 e (c2 ▸ h1))
  exact c2 ▸ (patchedModule_annihilator_le_comap_iff_ideal_le l L G0 T Λ n O r B u J D A W m hsurj Q c1).1 key

end UpperTheory.V.Pa
