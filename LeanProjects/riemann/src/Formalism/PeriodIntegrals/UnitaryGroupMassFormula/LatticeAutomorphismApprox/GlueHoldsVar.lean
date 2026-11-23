import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Reduce
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocInj
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.Gl

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists PI.UnitaryGroupMassFormula.AdIndexEq

theorem vec_ext (I : AutInst) (x y : Fin I.n → I.E ⊗[I.F] Af I.F)
    (h : ∀ v, PI.FinKW.vecV I v x = PI.FinKW.vecV I v y) : x = y := by
  funext i
  have h0 : x i - y i = 0 := PI.FinKW.local_vector_injective I (x i - y i) (fun v => by
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (h v) i))
  exact sub_eq_zero.1 h0

theorem vecV_smul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (a : I.E ⊗[I.F] Af I.F)
    (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (a • x) = PI.FinKW.psiV I v a • PI.FinKW.vecV I v x := by
  funext i
  simp [PI.FinKW.vecV, map_mul]

theorem vecV_sub (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (x - y) = PI.FinKW.vecV I v x - PI.FinKW.vecV I v y := by
  funext i
  simp [PI.FinKW.vecV, map_sub]

theorem val_nat (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (h : (N : 𝓞 F) ∉ v.asIdeal) : Valued.v ((N : v.adicCompletion F)) = 1 := by
  rw [← map_natCast (algebraMap F (v.adicCompletion F)) N, Formalism.UG.P.levelaf_valued_algebraMap,
    ← map_natCast (algebraMap (𝓞 F) F) N, HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact h

theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {m g : ℕ} (h : Nat.Coprime m g) (hg : (g : 𝓞 F) ∈ v.asIdeal) : (m : 𝓞 F) ∉ v.asIdeal := by
  intro hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * (m : ℤ) + b * (g : ℤ) : ℤ) : 𝓞 F) = 1 := by rw [hab, Int.cast_one]
  rw [← h1]
  push_cast
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hm) (v.asIdeal.mul_mem_left _ hg)

theorem finite_over (F : Type) [Field F] [NumberField F] {g : ℕ} (hg : 1 ≤ g) :
    {v : HeightOneSpectrum (𝓞 F) | (g : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hg0 : (g : 𝓞 F) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have h0 : Ideal.span {(g : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hg0
  exact (Ideal.finite_factors h0).subset (fun v hv => Ideal.dvd_span_singleton.2 hv)

theorem mL_one_le (I : AutInst) : mL I 1 ≤ I.Lf :=
  Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy)

theorem mem_mL (I : AutInst) (m : ℕ) {W : Fin I.n → I.E ⊗[I.F] Af I.F} (hW : W ∈ I.Lf) :
    (m : I.E ⊗[I.F] Af I.F) • W ∈ mL I m :=
  Submodule.subset_span ⟨W, hW, rfl⟩

open Classical in

theorem matV_listProd (I : AutInst) (loc : ∀ v, GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E))
    (Y : HeightOneSpectrum (𝓞 I.F) → I.Gf)
    (hY1 : ∀ v, matV I v (Y v : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = loc v)
    (hY2 : ∀ v, SuppAt I v (Y v)) (l : List (HeightOneSpectrum (𝓞 I.F))) (hl : l.Nodup)
    (w : HeightOneSpectrum (𝓞 I.F)) :
    matV I w (((l.map Y).prod : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) =
      if w ∈ l then loc w else 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, map_mul, ih hl.2]
    by_cases hw : w = v
    · subst hw
      simp [hY1, hl.1]
    · rw [hY2 v w hw]
      simp [hw]

theorem glue_holds_var : Glue := by
  intro hL I g r k e f z Rf hg hs hn hee hff hef hz ht hi hiz
  classical
  have hH : Hyps I g r k e f z := hyps_of hg hs hn hee hff hef hz ht hi hiz
  have hloc : ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      LocConcl I g r e f z Rf.z0 v := fun v hv => hL I g r k e f z Rf hH v hv
  let loc : ∀ v : HeightOneSpectrum (𝓞 I.F), GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) :=
    fun v => if hv : (g : 𝓞 I.F) ∈ v.asIdeal then Classical.choose (hloc v hv) else 1
  have hloc1 : ∀ v, (g : 𝓞 I.F) ∉ v.asIdeal → loc v = 1 := fun v hv => dif_neg hv
  have hspec : ∀ v (hv : (g : 𝓞 I.F) ∈ v.asIdeal), loc v = Classical.choose (hloc v hv) :=
    fun v hv => dif_pos hv
  have hlocUK : ∀ v, loc v ∈ Uv I v ∧ loc v ∈ Kv I v := by
    intro v
    by_cases hv : (g : 𝓞 I.F) ∈ v.asIdeal
    · obtain ⟨hU, hK, -⟩ := Classical.choose_spec (hloc v hv)
      rw [hspec v hv]
      exact ⟨hU, hK⟩
    · rw [hloc1 v hv]
      exact ⟨one_mem _, one_mem _⟩
  have hlocS : ∀ v, (g : 𝓞 I.F) ∈ v.asIdeal →
      (∀ a, ((loc v : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I (e a)) =
          PI.FinKW.vecV I v (incl I (e a)) ∧
        ((loc v : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I (f a)) =
          PI.FinKW.vecV I v (incl I (f a))) ∧
      ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
        (((loc v)⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I z) -
          PI.FinKW.vecV I v Rf.z0 = ((g : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) • w := by
    intro v hv
    obtain ⟨-, -, hfix, hw⟩ := Classical.choose_spec (hloc v hv)
    rw [hspec v hv]
    exact ⟨hfix, hw⟩
  have hY : ∀ v, ∃ y : I.Gf, matV I v (y : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = loc v ∧ SuppAt I v y :=
    fun v => lift_unitary' I v (loc v) (hlocUK v).1
  choose Y hY1 hY2 using hY
  have hfin := finite_over I.F hg
  let x : I.Gf := (hfin.toFinset.toList.map Y).prod
  have hx : ∀ w, matV I w (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) = loc w := by
    intro w
    rw [matV_listProd I loc Y hY1 hY2 _ (Finset.nodup_toList _) w]
    by_cases hw : (g : 𝓞 I.F) ∈ w.asIdeal
    · rw [if_pos (by simpa using hw)]
    · rw [if_neg (by simpa using hw), hloc1 w hw]
  have hxm : ∀ v, (I.fmat x).map (PI.FinKW.psiV I v).toRingHom =
      ((loc v : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) := by
    intro v
    rw [← hx v, matV_coe]
  have hxi : ∀ v, (I.fmat x⁻¹).map (PI.FinKW.psiV I v).toRingHom =
      (((loc v)⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) := by
    intro v
    rw [← hx v, ← map_inv, ← Subgroup.coe_inv, matV_coe]
  have hmulx : ∀ v (u : Fin I.n → I.E ⊗[I.F] Af I.F), PI.FinKW.vecV I v (I.fmat x *ᵥ u) =
      ((loc v : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v u := by
    intro v u
    rw [vecV_mulVec', hxm]
  have hmulxi : ∀ v (u : Fin I.n → I.E ⊗[I.F] Af I.F), PI.FinKW.vecV I v (I.fmat x⁻¹ *ᵥ u) =
      (((loc v)⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v u := by
    intro v u
    rw [vecV_mulVec', hxi]
  have hLf : ∀ W, (∀ v, PI.FinKW.vecV I v W ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) →
      W ∈ I.Lf := fun W hW => PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I W hW
  have hLt : ∀ W, W ∈ I.Lf → ∀ v,
      PI.FinKW.vecV I v W ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun W hW v => PI.FinKW.LocTo.mem_local_lattice_iff I W hW v
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  ·
    intro a
    constructor
    · apply vec_ext
      intro v
      rw [hmulx]
      by_cases hv : (g : 𝓞 I.F) ∈ v.asIdeal
      · exact ((hlocS v hv).1 a).1
      · rw [hloc1 v hv, Units.val_one, one_mulVec]
    · apply vec_ext
      intro v
      rw [hmulx]
      by_cases hv : (g : 𝓞 I.F) ∈ v.asIdeal
      · exact ((hlocS v hv).1 a).2
      · rw [hloc1 v hv, Units.val_one, one_mulVec]
  ·
    obtain ⟨c, hc, hcz⟩ := hiz
    have hcz' : (c : I.E ⊗[I.F] Af I.F) • incl I z ∈ I.Lf := mL_one_le I hcz
    have hz0 : Rf.z0 ∈ I.Lf := Rf.vectorsInLattice.2.1
    set u : Fin I.n → I.E ⊗[I.F] Af I.F := I.fmat x⁻¹ *ᵥ incl I z - Rf.z0 with hu
    have hgF : ((g : ℕ) : I.F) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
    set W : Fin I.n → I.E ⊗[I.F] Af I.F :=
      algebraMap I.F (I.E ⊗[I.F] Af I.F) ((g : I.F)⁻¹) • ((c : I.E ⊗[I.F] Af I.F) • u) with hWdef
    have hvW : ∀ v, PI.FinKW.vecV I v W = algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ((g : I.F)⁻¹) •
        ((c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) • PI.FinKW.vecV I v u) := by
      intro v
      rw [hWdef, vecV_smul, vecV_smul, AlgHom.commutes, map_natCast]
    have hscal : ∀ v, algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ((g : I.F)⁻¹) *
        ((g : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) = 1 := by
      intro v
      rw [← map_natCast (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) g, ← map_mul,
        inv_mul_cancel₀ hgF, map_one]
    have hW : W ∈ I.Lf := by
      apply hLf
      intro v
      by_cases hv : (g : 𝓞 I.F) ∈ v.asIdeal
      · obtain ⟨w, hw, hweq⟩ := (hlocS v hv).2
        have hvu : PI.FinKW.vecV I v u = ((g : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) • w := by
          rw [hu, vecV_sub, hmulxi]
          exact hweq
        have hA : algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ((g : I.F)⁻¹) *
            (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) * ((g : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) =
            (c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) := by
          rw [mul_right_comm, hscal v, one_mul]
        rw [hvW, hvu, smul_smul, smul_smul, hA, Nat.cast_smul_eq_nsmul]
        exact nsmul_mem hw c
      · have hval := val_nat I.F v g hv
        apply PI.UnitaryGroupMassFormula.AdIndexEq.cancel_nat v hval
        have hvu : PI.FinKW.vecV I v u = PI.FinKW.vecV I v (incl I z) - PI.FinKW.vecV I v Rf.z0 := by
          rw [hu, vecV_sub, hmulxi, hloc1 v hv, inv_one, Units.val_one, one_mulVec]
        have e1 : g • PI.FinKW.vecV I v W = PI.FinKW.vecV I v ((c : I.E ⊗[I.F] Af I.F) • incl I z) -
            c • PI.FinKW.vecV I v Rf.z0 := by
          rw [hvW, hvu, ← Nat.cast_smul_eq_nsmul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) g, smul_smul,
            mul_comm ((g : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E), hscal v, one_smul,
            smul_sub, vecV_smul, map_natCast,
            Nat.cast_smul_eq_nsmul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) c (PI.FinKW.vecV I v Rf.z0)]
        rw [e1]
        exact sub_mem (hLt _ hcz' v) (nsmul_mem (hLt _ hz0 v) c)
    refine ⟨c, hc, ?_⟩
    have hcu : (c : I.E ⊗[I.F] Af I.F) • u = ((g : ℕ) : I.E ⊗[I.F] Af I.F) • W := by
      rw [hWdef, smul_smul, ← map_natCast (algebraMap I.F (I.E ⊗[I.F] Af I.F)) g,
        ← map_mul, mul_inv_cancel₀ hgF, map_one, one_smul]
    rw [hcu]
    exact mem_mL I g hW
  ·
    intro m hm y hy
    set u : Fin I.n → I.E ⊗[I.F] Af I.F := (I.fmat x - 1) *ᵥ y with hu
    have hvu : ∀ v, PI.FinKW.vecV I v u =
        ((loc v : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v y -
          PI.FinKW.vecV I v y := by
      intro v
      rw [hu, Matrix.sub_mulVec, Matrix.one_mulVec, vecV_sub, hmulx]
    by_cases hm0 : m = 0
    · subst hm0
      have hg1 : g = 1 := (Nat.coprime_zero_left g).1 hm
      have hu0 : u = 0 := by
        apply vec_ext
        intro v
        have hv : (g : 𝓞 I.F) ∉ v.asIdeal := by
          rw [hg1, Nat.cast_one]
          exact fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
        rw [hvu, hloc1 v hv, Units.val_one, one_mulVec, sub_self]
        funext i
        simp [PI.FinKW.vecV]
      refine ⟨1, by simp, ?_⟩
      rw [hu0, smul_zero]
      exact zero_mem _
    have hmF : ((m : ℕ) : I.F) ≠ 0 := by exact_mod_cast hm0
    set W : Fin I.n → I.E ⊗[I.F] Af I.F :=
      algebraMap I.F (I.E ⊗[I.F] Af I.F) ((m : I.F)⁻¹) • u with hWdef
    have hW : W ∈ I.Lf := by
      apply hLf
      intro v
      have hvW : PI.FinKW.vecV I v W = algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) ((m : I.F)⁻¹) •
          PI.FinKW.vecV I v u := by
        rw [hWdef, vecV_smul, AlgHom.commutes]
      by_cases hv : (g : 𝓞 I.F) ∈ v.asIdeal
      · have hval := val_nat I.F v m (not_mem_of_coprime v hm hv)
        apply PI.UnitaryGroupMassFormula.AdIndexEq.cancel_nat v hval
        have e1 : m • PI.FinKW.vecV I v W = PI.FinKW.vecV I v u := by
          rw [hvW, ← Nat.cast_smul_eq_nsmul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) m, smul_smul,
            ← map_natCast (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) m, ← map_mul,
            mul_inv_cancel₀ hmF, map_one, one_smul]
        rw [e1, hvu]
        have hyv := hLt y hy v
        exact sub_mem (((hlocUK v).2 _).1 hyv) hyv
      · rw [hvW, hvu, hloc1 v hv, Units.val_one, one_mulVec, sub_self, smul_zero]
        exact zero_mem _
    refine ⟨1, by simp, ?_⟩
    have hmu : u = ((m : ℕ) : I.E ⊗[I.F] Af I.F) • W := by
      rw [hWdef, smul_smul, ← map_natCast (algebraMap I.F (I.E ⊗[I.F] Af I.F)) m, ← map_mul,
        mul_inv_cancel₀ hmF, map_one, one_smul]
    rw [Nat.cast_one, one_smul, hmu]
    exact mem_mL I m hW
  ·
    show (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    rw [stab_iff_loc]
    intro v
    rw [hx v]
    exact (hlocUK v).2

end PI.UnitaryGroupMassFormula.ScXuExists.Gl

end
