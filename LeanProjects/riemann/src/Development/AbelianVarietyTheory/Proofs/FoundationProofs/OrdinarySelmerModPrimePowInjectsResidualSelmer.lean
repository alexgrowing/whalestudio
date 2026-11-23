import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryInertiaIndependent
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelLower

variable {l : ℕ} [Fact l.Prime]

open Classical in

def rv (c : Coef l) (n : ℕ) (v : Fin 2 → Qbar l) : Mn c n :=
  fun i => if h : v i ∈ c.O then red c n ⟨v i, h⟩ else 0

theorem rv_apply {c : Coef l} {n : ℕ} {v : Fin 2 → Qbar l} (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    rv c n v i = red c n ⟨v i, hv i⟩ := by
  unfold rv; rw [dif_pos (hv i)]

theorem rv_eq_iff {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n a = rv c n b ↔ Cv n a b := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [rv_apply ha, rv_apply hb, red_eq_iff]

theorem addV {c : Coef l} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    ∀ i, (a + b) i ∈ c.O := fun i => c.O.add_mem (ha i) (hb i)

theorem subV {c : Coef l} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    ∀ i, (a - b) i ∈ c.O := fun i => c.O.sub_mem (ha i) (hb i)

theorem zeroV (c : Coef l) : ∀ i, (0 : Fin 2 → Qbar l) i ∈ c.O := fun _ => c.O.zero_mem

theorem rv_add {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n (a + b) = rv c n a + rv c n b := by
  funext i
  rw [rv_apply (addV ha hb)]
  show _ = rv c n a i + rv c n b i
  rw [rv_apply ha, rv_apply hb, ← map_add]
  rfl

theorem rv_sub {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n (a - b) = rv c n a - rv c n b := by
  funext i
  rw [rv_apply (subV ha hb)]
  show _ = rv c n a i - rv c n b i
  rw [rv_apply ha, rv_apply hb, ← map_sub]
  rfl

theorem rv_zero (c : Coef l) (n : ℕ) : rv c n 0 = 0 := by
  funext i
  rw [rv_apply (zeroV c)]
  show _ = (0 : Qn c n)
  rw [← map_zero (red c n)]
  rfl

theorem mulVec_mem {c : Coef l} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O)
    {x : Fin 2 → Qbar l} (hx : ∀ i, x i ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM _ _) (hx _)) (c.O.mul_mem (hM _ _) (hx _))

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem rv_mulVec (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω)
    {x : Fin 2 → Qbar l} (hx : ∀ i, x i ∈ c.O) :
    rv c n (mat W s *ᵥ x) = matQ c n W hint s *ᵥ rv c n x := by
  funext i
  rw [rv_apply (mulVec_mem (hint s) hx)]
  have e : (⟨(mat W s *ᵥ x) i, mulVec_mem (hint s) hx i⟩ : c.O) =
      ⟨mat W s i 0, hint s i 0⟩ * ⟨x 0, hx 0⟩ + ⟨mat W s i 1, hint s i 1⟩ * ⟨x 1, hx 1⟩ := by
    apply Subtype.ext
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e, map_add, map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, matQ_apply, rv_apply hx]

theorem continuous_rv (c : Coef l) (n : ℕ) {y : G ℚ Ω → Fin 2 → Qbar l} (hyc : Continuous y)
    (hO : ∀ s i, y s i ∈ c.O) : Continuous fun s => rv c n (y s) := by
  refine continuous_pi fun i => ?_
  refine continuous_discrete_rng.2 fun q => ?_
  obtain ⟨z, rfl⟩ := red_surjective c n q
  have e : (fun s => rv c n (y s) i) ⁻¹' {red c n z} =
      (fun s => y s i) ⁻¹' Metric.closedBall (z : Qbar l) ‖((l : ℕ) : Qbar l) ^ n‖ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm, rv_apply (hO s)]
    exact red_eq_iff _ _
  rw [e]
  have hne : ‖((l : ℕ) : Qbar l) ^ n‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (IsUltrametricDist.isOpen_closedBall _ hne).preimage ((continuous_apply i).comp hyc)

theorem eq_of_natCast_mem {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) :
    v = w := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
      (Nat.prime_iff_prime_int.1 (Fact.out : l.Prime))
  have hmax : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  have h1 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)
  have h2 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)
  exact HeightOneSpectrum.ext (h1.symm.trans h2)

theorem toGS_surjective (S : Finset Pl) : Function.Surjective (toGS Ω (S : Set Pl)) :=
  QuotientGroup.mk'_surjective _

def zOf (c : Coef l) (n : ℕ) (S : Finset Pl) (y : G ℚ Ω → Fin 2 → Qbar l) : GS Ω (S : Set Pl) → Mn c n :=
  fun g => rv c n (y (Function.surjInv (toGS_surjective S) g))

theorem rv_wd (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) {y : G ℚ Ω → Fin 2 → Qbar l} (hy : GwCount.SelN c n S A W y)
    {s t : G ℚ Ω} (h : toGS Ω (S : Set Pl) s = toGS Ω (S : Set Pl) t) : rv c n (y s) = rv c n (y t) := by
  have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
  have ha : s⁻¹ * t ∈ (toGS Ω (S : Set Pl)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have e : s * (s⁻¹ * t) = t := by group
  have h1 := hy.1.2.2 s (Subgroup.mem_top _) (s⁻¹ * t) (Subgroup.mem_top _)
  rw [e] at h1
  have h2 := hy.2.1 _ ha
  rw [(rv_eq_iff (hO t) (addV (hO s) (mulVec_mem (hint s) (hO _)))).2 h1,
    rv_add (hO s) (mulVec_mem (hint s) (hO _)), rv_mulVec c n W hint s (hO _),
    (rv_eq_iff (hO _) (zeroV c)).2 h2, rv_zero, Matrix.mulVec_zero, add_zero]

theorem zOf_toGS (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) {y : G ℚ Ω → Fin 2 → Qbar l} (hy : GwCount.SelN c n S A W y)
    (s : G ℚ Ω) : zOf c n S y (toGS Ω (S : Set Pl) s) = rv c n (y s) :=
  rv_wd c n S A W hint hy (Function.surjInv_eq (toGS_surjective S) _)

theorem zOf_mem (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (A : ValuationSubring Ω) {y : G ℚ Ω → Fin 2 → Qbar l}
    (hy : GwCount.SelN c n S A W y) : zOf c n S y ∈ Z1 (rhoS c n W hint S hN) := by
  have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
  refine ⟨?_, fun g h => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have e : (zOf c n S y ∘ QuotientGroup.mk) = fun s => rv c n (y s) :=
      funext fun s => zOf_toGS c n S A W hint hy s
    rw [e]
    have h0 := hy.1.1
    rw [Subgroup.coe_top] at h0
    exact continuous_rv c n (continuousOn_univ.1 h0) hO
  · obtain ⟨s, rfl⟩ := toGS_surjective S g
    obtain ⟨t, rfl⟩ := toGS_surjective S h
    rw [← map_mul, zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy,
      rhoS_toGS, ← rv_mulVec c n W hint s (hO t), ← rv_add (hO s) (mulVec_mem (hint s) (hO t))]
    exact (rv_eq_iff (hO _) (addV (hO s) (mulVec_mem (hint s) (hO t)))).2
      (hy.1.2.2 s (Subgroup.mem_top _) t (Subgroup.mem_top _))

end

theorem sel_lower : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∃ cls : (G ℚ Ω → Fin 2 → Qbar l) → H1 (rhoS c n W hint S hN), (∀ y, GwCount.SelN c n S A W y → cls y ∈ SelG c n W hint S hN A) ∧ ∀ y y', GwCount.SelN c n S A W y → GwCount.SelN c n S A W y' → cls y = cls y' → Cob1 c n W ⊤ (y - y') := by
  intro l _ Ω _ _ _ e S A W hW c hint hN n _
  classical
  refine ⟨fun y => if h : GwCount.SelN c n S A W y then
    Submodule.Quotient.mk ⟨zOf c n S y, zOf_mem c n W hint S hN A h⟩ else 0, ?_, ?_⟩
  · intro y hy
    have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
    simp only [dif_pos hy]
    rw [SelG, mem_Sel]
    intro v
    rw [resH1, Submodule.mapQ_apply]
    by_cases hv : IsPlaceOver A v.1
    · have hL : Lc c n W hint S hN A v = ordCond c n W hint S hN (Av A S v) := by
        unfold Lc; exact if_pos hv
      have hAv : Av A S v = A := by
        unfold Av; rw [if_pos hv]
      rw [hL]
      change Submodule.Quotient.mk (restrictCocycles1 (rhoS c n W hint S hN) (locHom (S : Set Pl) (Av A S v))
        (continuous_locHom _ _) ⟨zOf c n S y, zOf_mem c n W hint S hN A hy⟩) ∈ ordCond c n W hint S hN (Av A S v)
      rw [ordCond]
      have hmem : restrictCocycles1 (rhoS c n W hint S hN) (locHom (S : Set Pl) (Av A S v)) (continuous_locHom _ _)
          ⟨zOf c n S y, zOf_mem c n W hint S hN A hy⟩ ∈
          (ordZ c n W hint (Av A S v)).comap (Z1 ((rhoS c n W hint S hN).comp
            (locHom (S : Set Pl) (Av A S v)))).subtype := by
        rw [Submodule.mem_comap, mem_ordZ]
        obtain ⟨x, hx, hxs⟩ := hy.2.2.2
        refine ⟨red c n ⟨x, hx⟩, fun s => ?_⟩
        show zOf c n S y (toGS Ω (S : Set Pl) s.1) 1 = _
        have hs : (s : G ℚ Ω) ∈ Dec (F := ℚ) A := (le_of_eq (congrArg (Dec (F := ℚ)) hAv)) s.2
        rw [zOf_toGS c n S A W hint hy, rv_apply (hO s.1), matQ_apply, ← map_mul, ← map_sub, red_eq_iff]
        exact hxs s hs
      exact Submodule.mem_map_of_mem hmem
    · have hL : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
          ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := by
        unfold Lc; exact if_neg hv
      have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.1.asIdeal := fun h => hv (by
        obtain ⟨v0, hA0, hl0⟩ := hW.atL
        rw [eq_of_natCast_mem h hl0]
        exact hA0)
      obtain ⟨B, hB, hcob⟩ := hy.2.2.1 v.1 v.2 hl
      obtain ⟨x, hxO, hx⟩ := CobConj.cob_conj l Ω W c n y v.1 B (Av A S v) hint hy.1 hB
        (isPlaceOver_Av A S v) hcob
      rw [hL, H1ur, LinearMap.mem_ker]
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨rv c n x, fun g => ?_⟩)
      show zOf c n S y (toGS Ω (S : Set Pl) g.1.1) = matQ c n W hint g.1.1 *ᵥ rv c n x - rv c n x
      have hg : (g.1.1 : G ℚ Ω) ∈ Ine (F := ℚ) (Av A S v) := Subgroup.mem_subgroupOf.1 g.2
      rw [zOf_toGS c n S A W hint hy, ← rv_mulVec c n W hint _ hxO, ← rv_sub (mulVec_mem (hint _) hxO) hxO]
      exact (rv_eq_iff (hO _) (subV (mulVec_mem (hint _) hxO) hxO)).2 (hx _ hg)
  · intro y y' hy hy' heq
    have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
    have hO' : ∀ s i, y' s i ∈ c.O := hy'.1.2.1
    simp only [dif_pos hy, dif_pos hy'] at heq
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at heq
    obtain ⟨m, hm⟩ := heq
    choose x hx using fun i => red_surjective c n (m i)
    have hxO : ∀ i, (fun i => ((x i : c.O) : Qbar l)) i ∈ c.O := fun i => (x i).2
    have hm' : rv c n (fun i => ((x i : c.O) : Qbar l)) = m := funext fun i => by
      rw [rv_apply hxO]; exact hx i
    refine ⟨fun i => ((x i : c.O) : Qbar l), hxO, fun s _ => ?_⟩
    have h := hm (toGS Ω (S : Set Pl) s)
    change zOf c n S y (toGS Ω (S : Set Pl) s) - zOf c n S y' (toGS Ω (S : Set Pl) s) =
      rhoS c n W hint S hN (toGS Ω (S : Set Pl) s) m - m at h
    rw [zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy', rhoS_toGS, ← hm',
      ← rv_mulVec c n W hint s hxO, ← rv_sub (hO s) (hO' s), ← rv_sub (mulVec_mem (hint s) hxO) hxO] at h
    exact (rv_eq_iff (subV (hO s) (hO' s)) (subV (mulVec_mem (hint s) hxO) hxO)).1 h

end GlobalTheory.Ord2.SelLower
