import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvMemOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist

namespace Formalism.FourierDecayAlt.P.TLB

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
  Formalism.YangianSpanCharacter.T

noncomputable section

section gen

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem tprod_take_all (L : LevelData A r) (Y : ℂ) :
    L.Tprod Y = ((List.ofFn (L.Tl Y)).take r).reverse.prod := by
  unfold LevelData.Tprod
  rw [List.take_of_length_le (by simp)]

variable [StarRing A] [StarModule ℂ A]

theorem star_algMap (z : ℂ) : star (algebraMap ℂ A z) = algebraMap ℂ A (starRingEnd ℂ z) := by
  rw [← algebraMap_star_comm]; rfl

theorem star_Tl_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) (l : Fin r) :
    (L.Tl y l)ᴴ = (L.Tvl (starRingEnd ℂ y) l)ᵀ := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, LevelData.Tvl, conjTranspose_apply, star_add, star_neg, hp, hc, hci, star_algMap,
      sub_eq_add_neg]

theorem star_Tprod_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) :
    (L.Tprod y)ᴴ = (L.Tvprod (starRingEnd ℂ y))ᵀ := by
  rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose]
  unfold LevelData.Tprod
  rw [conjTranspose_list_prod, List.map_reverse, List.reverse_reverse, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun l => star_Tl_gen L hp hc hci y l)

end gen

section actual

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rma_pref_take (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) :
    ∀ n, Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n = ((List.ofFn (L.Tl Y)).take n).reverse.prod
  | 0 => by simp [Formalism.FourierDecayAlt.P.JCx2.rma_pref]
  | n + 1 => by
    by_cases h : n < r
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dif_pos h, rma_pref_take L Y n, List.take_add_one, List.reverse_append,
        List.prod_append]
      have e : (List.ofFn (L.Tl Y))[n]? = some (L.Tl Y ⟨n, h⟩) := by simp [h]
      rw [e]
      simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons,
        List.prod_nil, mul_one]
      congr 1
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dif_neg h, rma_pref_take L Y n, List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by simp; omega)]

theorem tprod_zero_eq (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) : tprod L Y 0 = L.Tprod Y := by
  have h : tprod L Y 0 = Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y r := by
    have := Formalism.FourierDecayAlt.P.JCx2.rma_tprod_pref L Y r 0 (by omega)
    simpa [Formalism.FourierDecayAlt.P.JCx2.rma_pref] using this
  rw [h, rma_pref_take, tprod_take_all]

end actual

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

noncomputable section

theorem actual_algebra_facts : TL.ActualAlg := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  have hD' := hD
  obtain ⟨hpl, -, hL, hQQ, -, -, hSL, hst⟩ := hD
  obtain ⟨sp, sc, sci⟩ := P5.HerA.star_site_ops hL
  have hcent : ∀ (l : Fin P.r) (Y : ℂ) (a b : Fin 2),
      st.QQ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    intro l Y a b
    obtain ⟨hp, -, hc, hci, -⟩ := hL
    have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
      fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
    have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
      intro i Y a b; rw [mul_neg, neg_mul, ht]
    rw [hQQ Y, Matrix.smul_apply]
    refine SMulMemClass.smul_mem _ ?_
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hp l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), P5.HerA.pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hc l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hci l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
  have hqq : ∀ Y i j, ∀ x ∈ siteOps L, Commute (st.QQ Y i j) x := by
    intro Y i j x hx
    have key := fun l => (StarSubalgebra.mem_centralizer_iff ℂ).1 (hcent l Y i j)
    simp only [siteOps, Set.mem_union, Set.mem_range] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
    · have h := key l
      exact (h (L.p l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.p l) (by simp [hol, site])).2
      rw [sp l] at h2
      exact Commute.neg_right_iff.1 (show Commute (st.QQ Y i j) (-L.pb l) from h2.symm)
    · exact (key l (L.c l) (by simp [hol, site])).1.symm
    · exact (key l (L.ci l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.c l) (by simp [hol, site])).2
      rw [sc l] at h2
      exact h2.symm
    · have h2 := (key l (L.ci l) (by simp [hol, site])).2
      rw [sci l] at h2
      exact h2.symm
  refine ⟨⟨hSL, hst, sp, sc, sci, hqq⟩, fun Y hY => ?_, fun Y hY => ?_⟩
  · have hY' : starRingEnd ℂ Y = Y := hY
    unfold P5.QQi
    simp only [Fin.val_zero]
    rw [hY, TLB.tprod_zero_eq, TLB.star_Tprod_gen L sp sc sci, hY']
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, cst, nP, LevelData.Ar, LevelData.Br,
      LevelData.Avr, LevelData.Bvr]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  · obtain ⟨κ, hx, hxi, -⟩ :=
      P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD'
    classical
    set f : M.Ty P → ℂ := fun ρ => M.x0 P l0 ρ Y with hf
    set N : Finset ℂ := Finset.univ.image f
    set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
    have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
      intro ρ
      have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
      have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
      simpa only [id] using h
    have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
      funext ρ
      rw [← hp ρ]
      have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : M.Ty P => ℂ) ρ) f p
      rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
      rw [this]
      rfl
    refine ⟨p, ?_⟩
    rw [hxi Y hY, hx Y, Polynomial.aeval_algHom_apply]
    exact congrArg κ he

end

end Formalism.FourierDecayAlt.P
