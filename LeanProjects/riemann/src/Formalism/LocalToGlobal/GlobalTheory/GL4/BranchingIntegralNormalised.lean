import Formalism.LocalToGlobal.GlobalTheory.GL4.MapIntRatComplex

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

theorem sgNat_anti {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) : Antitone (sgNat sg) := by
  rw [sgNat_eq lt sg h0 hI]
  exact fun a b h => Nat.add_le_add_right (natW_anti sg h) _

theorem lamNat_anti {n : ℕ} (lt : DomWeight (n + 1)) : Antitone (lamNat lt) :=
  fun _ _ h => natW_anti lt (Fin.castSucc_le_castSucc_iff.mpr h)

theorem twist_dualQ {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) (v : MvPolynomial (Fin n × Fin n) ℚ) (hv : v ∈ dualWeyl ℚ n n sg.natW) :
    dpowR ℚ n sg.detShift.toNat * v ∈ weyl ℚ n n le_rfl (sgNat sg) := by
  rw [← Formalism.GradedWeylDivisibility.weylEqNablaQ n n le_rfl _ (natW_anti sg)] at hv
  exact twist_mem_gen ℚ lt sg h0 hI v hv

theorem twist_dualZ {n : ℕ} (lt : DomWeight (n + 1)) (sg : DomWeight n) (h0 : lt.w (Fin.last n) = 0)
    (hI : Interlace lt sg) (q : MvPolynomial (Fin n × Fin n) ℤ) (hq : q ∈ dualWeyl ℤ n n sg.natW) :
    dpowR ℤ n sg.detShift.toNat * q ∈ dualWeyl ℤ n n (sgNat sg) := by
  rw [Formalism.GradedWeylDivisibility.dualWeylIntRat, map_mul, map_dpowR]
  exact Formalism.GradedWeylDivisibility.weylLeDual ℚ n n le_rfl _ (sgNat_anti lt sg h0 hI)
    (twist_dualQ lt sg h0 hI _ (Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℚ _ n n _ q hq))

theorem fockF_zero_right' {κ : Type} (f : MvPolynomial κ ℂ) : fockF f 0 = 0 := by
  have := fockF_smul_right_eq_star_mul (0 : ℂ) f 0
  simpa using this

theorem adjoint_integrality : AdjointIntegrality := by
  intro n lt sg h0 hI io hio1 hio2 hio3 hio4 P hPV hPadj F hF
  have hInter := interlace_nat lt sg h0 hI
  obtain ⟨ioQ, hQ1, hQ2, hQ3, -⟩ := Formalism.BranchingDeterminantCap.branch_map_formula ℚ n (lamNat lt) (sgNat sg) hInter
  obtain ⟨ioZ, hZ1, hZ2, hZ3, -⟩ := Formalism.BranchingDeterminantCap.branch_map_formula ℤ n (lamNat lt) (sgNat sg) hInter
  have hs := sgNat_anti lt sg h0 hI
  have hs' := natW_anti sg
  have hlam := lamNat_anti lt
  rw [delSq_eq_map ℤ lt] at hF
  obtain ⟨F0, hF0, rfl⟩ := hF
  change F0 ∈ weyl ℤ (n + 1) n (Nat.le_succ n) (lamNat lt) at hF0
  set c := sg.detShift.toNat with hc
  set V := weyl ℚ n n le_rfl sg.natW with hV
  have hVd : V = dualWeyl ℚ n n sg.natW := Formalism.GradedWeylDivisibility.weylEqNablaQ n n le_rfl _ hs'
  have : FiniteDimensional ℚ V := by rw [hVd]; exact Formalism.GradedWeylDivisibility.lclosedeq_fd n n _
  have hmemQ : ∀ v ∈ V, dpowR ℚ n c * v ∈ dualWeyl ℚ n n (sgNat sg) := fun v hv =>
    Formalism.GradedWeylDivisibility.weylLeDual ℚ n n le_rfl _ hs (twist_mem_gen ℚ lt sg h0 hI v hv)
  let twQ : V →ₗ[ℚ] ↥(dualWeyl ℚ n n (sgNat sg)) :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft ℚ (dpowR ℚ n c)).comp V.subtype) (fun v => hmemQ v v.2)
  have htwQ : ∀ v : V, ((twQ v : ↥(dualWeyl ℚ n n (sgNat sg))) : MvPolynomial (Fin n × Fin n) ℚ) =
      dpowR ℚ n c * (v : MvPolynomial (Fin n × Fin n) ℚ) := fun _ => rfl
  set F0q := map (Int.castRingHom ℚ) F0 with hF0q
  set ns := fockQ (hw ℚ le_rfl sg.natW) (hw ℚ (r := n) le_rfl sg.natW) with hns
  set nl := fockQ (hw ℚ (Nat.le_succ n) (lamNat lt)) (hw ℚ (Nat.le_succ n) (lamNat lt)) with hnl
  have hns0 : 0 < ns := fockQ_hw_pos _ _
  have hnl0 : 0 < nl := fockQ_hw_pos _ _
  let φ : V →ₗ[ℚ] ℚ := (ns / nl) • ((fockQLin F0q).comp (ioQ.comp twQ))
  have hφ : ∀ v : V, φ v = ns / nl * fockQ (ioQ (twQ v)) F0q := fun _ => rfl
  obtain ⟨p, hpV, hp⟩ := rieszQ V φ

  have hbd : p ∈ bDual n n le_rfl sg.natW ((dualWeyl ℤ n n sg.natW).map (intQ n n)) := by
    refine ⟨hVd ▸ hpV, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    have hqQ : intQ n n q ∈ V := by
      rw [hVd]
      exact Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℚ _ n n _ q hq
    have e := hp ⟨_, hqQ⟩
    rw [hφ] at e
    have h1 : dpowR ℤ n c * q ∈ dualWeyl ℤ n n (sgNat sg) := twist_dualZ lt sg h0 hI q hq
    have h2 : map (Int.castRingHom ℚ) (dpowR ℤ n c * q) ∈ dualWeyl ℚ n n (sgNat sg) :=
      Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℚ _ n n _ _ h1
    have etw : twQ ⟨_, hqQ⟩ = ⟨_, h2⟩ := by
      apply Subtype.ext
      rw [htwQ]
      show dpowR ℚ n c * intQ n n q = map (Int.castRingHom ℚ) (dpowR ℤ n c * q)
      rw [map_mul, map_dpowR, intQ_apply]
    obtain ⟨N, hN, hNq⟩ := nablaZ_denom le_rfl (sgNat sg) hs _ h1
    have ebc := io_bc (Int.castRingHom ℚ) Int.cast_injective (lamNat lt) (sgNat sg) hs ioZ hZ2 hZ3 ioQ hQ2 hQ3
      (dpowR ℤ n c * q) N hN hNq h1 h2
    rw [etw, ebc] at e
    have hF0b : intQ (n + 1) n F0 ∈
        bDual (n + 1) n (Nat.le_succ n) (lamNat lt) ((dualWeyl ℤ (n + 1) n (lamNat lt)).map (intQ (n + 1) n)) := by
      rw [← weylEqDualNabla_holds (n + 1) n (Nat.le_succ n) (lamNat lt) hlam]
      exact ⟨F0, hF0, rfl⟩
    obtain ⟨z, hz⟩ := hF0b.2 _ ⟨ioZ ⟨_, h1⟩, hZ1 _, rfl⟩
    refine ⟨z, ?_⟩
    rw [intQ_apply, intQ_apply] at hz
    change _ = (z : ℚ) * nl at hz
    change fockQ p (intQ n n q) = _ at e
    show fockQ p (intQ n n q) = (z : ℚ) * ns
    rw [e, fockQ_comm, hz]
    field_simp
  rw [← weylEqDualNabla_holds n n le_rfl sg.natW hs'] at hbd
  obtain ⟨g, hg, hgp⟩ := hbd
  refine ⟨g, hg, ?_⟩
  rw [intQ_apply] at hgp
  show P (map (Int.castRingHom ℂ) (rename (colEmb (n + 1) n) F0)) = _
  rw [← map_int_rat_complex g, hgp]
  obtain ⟨tw1, -, -⟩ := twist_facts lt sg h0 hI
  refine eq_of_fock (delSq ℂ n sg) _ _ (hPV _) (Formalism.BranchingDeterminantCap.bs_map_weyl le_rfl sg.natW p hpV) ?_
  intro v hv
  unfold delSq weyl at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, rfl⟩ := hv
    set vq := applyWord ℚ w (hw ℚ (r := n) le_rfl sg.natW) with hvq
    have hvqV : vq ∈ V := Submodule.subset_span ⟨w, rfl⟩
    have hvmap : applyWord ℂ w (hw ℂ (r := n) le_rfl sg.natW) = map (algebraMap ℚ ℂ) vq := by
      rw [hvq, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
    have hvC : map (algebraMap ℚ ℂ) vq ∈ delSq ℂ n sg := Formalism.BranchingDeterminantCap.bs_map_weyl le_rfl sg.natW vq hvqV
    have hy : dpow n sg.detShift.toNat * map (algebraMap ℚ ℂ) vq ∈ dualWeyl ℂ n n (sgNat sg) :=
      Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ hs (tw1 _ hvC)
    change fockF _ (applyWord ℂ w (hw ℂ (r := n) le_rfl sg.natW)) = fockF _ (applyWord ℂ w (hw ℂ (r := n) le_rfl sg.natW))
    rw [hvmap]
    have e := hPadj (map (Int.castRingHom ℂ) (rename (colEmb (n + 1) n) F0)) _ hvC hy
    have h2 : map (algebraMap ℚ ℂ) ((twQ ⟨vq, hvqV⟩ : ↥(dualWeyl ℚ n n (sgNat sg))) : MvPolynomial (Fin n × Fin n) ℚ) ∈
        dualWeyl ℂ n n (sgNat sg) := Formalism.GradedWeylDivisibility.dualWeylMap ℚ ℂ _ n n _ _ (twQ ⟨vq, hvqV⟩).2
    have esub : (⟨_, hy⟩ : ↥(dualWeyl ℂ n n (sgNat sg))) = ⟨_, h2⟩ := by
      apply Subtype.ext
      show dpow n sg.detShift.toNat * map (algebraMap ℚ ℂ) vq = map (algebraMap ℚ ℂ) (dpowR ℚ n c * vq)
      rw [map_mul, map_dpowR]
      rfl
    have hw1 : (1 : ℚ) • ((twQ ⟨vq, hvqV⟩ : ↥(dualWeyl ℚ n n (sgNat sg))) : MvPolynomial (Fin n × Fin n) ℚ) ∈
        weyl ℚ n n le_rfl (sgNat sg) := by
      rw [one_smul]
      exact twist_mem_gen ℚ lt sg h0 hI vq hvqV
    have ebc := io_bc (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective (lamNat lt) (sgNat sg) hs ioQ hQ2 hQ3 io hio2 hio3
      _ 1 one_ne_zero hw1 (twQ ⟨vq, hvqV⟩).2 h2
    rw [esub, ebc] at e
    have eF : map (Int.castRingHom ℂ) (rename (colEmb (n + 1) n) F0) =
        rename (colEmb (n + 1) n) (map (algebraMap ℚ ℂ) F0q) := by
      rw [hF0q, map_int_rat_complex, map_rename]
    have eext1 : extremal ℂ n sg = map (algebraMap ℚ ℂ) (hw ℚ le_rfl sg.natW) := by
      rw [lclosedeq_hw_map]; rfl
    have eext2 : extremal ℂ (n + 1) lt =
        rename (colEmb (n + 1) n) (map (algebraMap ℚ ℂ) (hw ℚ (Nat.le_succ n) (lamNat lt))) := by
      rw [lclosedeq_hw_map]
      exact hw_rename ℂ lt.natW (natW_last lt)
    unfold normFock at e
    rw [eext1, eext2, eF, fockF_rename _ (colEmb_inj _ _), fockF_rename _ (colEmb_inj _ _),
      leadj_fockF_map, leadj_fockF_map, leadj_fockF_map] at e
    change _ / ((ns : ℚ) : ℂ) = _ / ((nl : ℚ) : ℂ) at e
    rw [eF, leadj_fockF_map, hp ⟨vq, hvqV⟩, hφ]
    have hnsC : ((ns : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hns0.ne'
    have hnlC : ((nl : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hnl0.ne'
    rw [div_eq_iff hnsC] at e
    rw [e, fockQ_comm F0q]
    push_cast
    field_simp
  | zero => rw [fockF_zero_right', fockF_zero_right']
  | add x y _ _ ihx ihy => rw [fockF_add_right_g_l4, fockF_add_right_g_l4, ihx, ihy]
  | smul a x _ ihx => rw [fockF_smul_right_eq_star_mul, fockF_smul_right_eq_star_mul, ihx]

theorem branching_link_all : Link3 := branching_link_of_adjoint adjoint_integrality

theorem branching_link_all_families : Link3F := branching_family_of_adjoint adjoint_integrality

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
