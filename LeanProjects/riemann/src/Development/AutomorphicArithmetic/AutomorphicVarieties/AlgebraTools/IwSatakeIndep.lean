import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkTrace
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBruhatKO
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFactTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

section SlopeTestRemainingChoices

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

private theorem double_coset_operator_sum_orbit (ρ : Representation A G M) (K K' : Subgroup G) (x : G) (h : FinOrb K K' x)
    [Fintype (MulAction.orbit K (x : G ⧸ K'))] (v : fixd ρ K') :
    (hk2 ρ K K' x v : M) = ∑ q : MulAction.orbit K (x : G ⧸ K'), ρ (q : G ⧸ K').out v := by
  rw [(hkApply A G M ρ K K' x h).1 v, dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

private noncomputable def permRepBaseCosetVector (A : Type) [CommRing A] (I : Subgroup G) : fixd (permRep A I) I :=
  ⟨MonoidAlgebra.single ((1 : G) : G ⧸ I) 1, fun u hu => by
    rw [Representation.ofMulAction_single]
    congr 1
    change ((u * 1 : G) : G ⧸ I) = _
    exact QuotientGroup.eq.mpr (by simpa using hu)⟩

open Classical in
private theorem satInd_trc {I K : Subgroup G} (h : I ≤ K) (hf : FinOrb K I 1) (g y : G) :
    (permRep A I g (trc (permRep A I) K I (permRepBaseCosetVector A I) : MonoidAlgebra A (G ⧸ I))).coeff (y : G ⧸ I) =
      if g⁻¹ * y ∈ K then 1 else 0 := by
  haveI : Fintype (MulAction.orbit K ((1 : G) : G ⧸ I)) := hf.fintype
  have hv : ((trc (permRep A I) K I (permRepBaseCosetVector A I) : fixd (permRep A I) K) : MonoidAlgebra A (G ⧸ I)) =
      ∑ q : MulAction.orbit K ((1 : G) : G ⧸ I), MonoidAlgebra.single (q : G ⧸ I) (1 : A) := by
    rw [trc, double_coset_operator_sum_orbit _ K I 1 hf]
    refine Finset.sum_congr rfl fun q _ => ?_
    show permRep A I _ (MonoidAlgebra.single ((1 : G) : G ⧸ I) 1) = _
    rw [Representation.ofMulAction_single]
    congr 1
    show (((q : G ⧸ I).out * 1 : G) : G ⧸ I) = _
    rw [mul_one, QuotientGroup.out_eq']
  rw [hv, map_sum, MonoidAlgebra.coeff_sum]
  simp only [Representation.ofMulAction_single, MonoidAlgebra.coeff_single, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  have key : ∀ q : MulAction.orbit K ((1 : G) : G ⧸ I),
      (g • (q : G ⧸ I) = (y : G ⧸ I)) ↔ (q : G ⧸ I) = ((g⁻¹ * y : G) : G ⧸ I) := by
    intro q
    rw [smul_eq_iff_eq_inv_smul]
    rfl
  simp only [key]
  by_cases hy : g⁻¹ * y ∈ K
  · rw [if_pos hy]
    have hmem : ((g⁻¹ * y : G) : G ⧸ I) ∈ MulAction.orbit K ((1 : G) : G ⧸ I) :=
      MulAction.mem_orbit_iff.2 ⟨⟨g⁻¹ * y, hy⟩, by
        show (((g⁻¹ * y : G) * 1 : G) : G ⧸ I) = _
        rw [mul_one]⟩
    have e2 : ∀ q : MulAction.orbit K ((1 : G) : G ⧸ I),
        (q : G ⧸ I) = ((g⁻¹ * y : G) : G ⧸ I) ↔ q = ⟨_, hmem⟩ :=
      fun q => ⟨fun hq => Subtype.ext hq, fun hq => by rw [hq]⟩
    simp only [e2]
    rw [Finset.sum_ite_eq']
    simp
  · rw [if_neg hy]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hq
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 q.2
    have h1 : (((k : G) * 1 : G) : G ⧸ I) = ((g⁻¹ * y : G) : G ⧸ I) := hk.trans hq
    rw [QuotientGroup.eq] at h1
    apply hy
    have := K.mul_mem k.2 (h h1)
    simpa using this

private theorem satInd_abs {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I) (hf : FinOrb K I 1)
    (e : HkAlg A I) (he : e.1 = inc (permRep A I) h ∘ₗ trc (permRep A I) K I) {ι : Type} (t : ι → G)
    (H : ∀ a b, ∀ i ∈ I, (i * t a)⁻¹ * t b ∈ K → a = b ∧ (i * t a)⁻¹ * t a ∈ I) :
    LinearIndependent A fun a => hT A I (t a) * e := by
  classical
  have key : ∀ a b, (((hT A I (t a) * e).1 (permRepBaseCosetVector A I) : fixd (permRep A I) I) :
      MonoidAlgebra A (G ⧸ I)).coeff ((t b : G) : G ⧸ I) = if a = b then 1 else 0 := by
    intro a b
    haveI : Fintype (MulAction.orbit I ((t a : G) : G ⧸ I)) := (hI (t a)).fintype
    have h1 : (((hT A I (t a) * e).1 (permRepBaseCosetVector A I) : fixd (permRep A I) I) : MonoidAlgebra A (G ⧸ I)) =
        ∑ q : MulAction.orbit I ((t a : G) : G ⧸ I), permRep A I (q : G ⧸ I).out
          ((trc (permRep A I) K I (permRepBaseCosetVector A I) : fixd (permRep A I) K) : MonoidAlgebra A (G ⧸ I)) := by
      show ((hk2 (permRep A I) I I (t a) (e.1 (permRepBaseCosetVector A I)) : fixd (permRep A I) I) :
        MonoidAlgebra A (G ⧸ I)) = _
      rw [double_coset_operator_sum_orbit _ I I (t a) (hI (t a)), he]
      rfl
    rw [h1, MonoidAlgebra.coeff_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    simp only [satInd_trc h hf]
    have hq : ∀ q : MulAction.orbit I ((t a : G) : G ⧸ I), ((q : G ⧸ I).out⁻¹ * t b ∈ K ↔
        (a = b ∧ q = ⟨((t a : G) : G ⧸ I), MulAction.mem_orbit_self _⟩)) := by
      intro q
      obtain ⟨i, hi⟩ := MulAction.mem_orbit_iff.1 q.2
      have hqi : (((i : G) * t a : G) : G ⧸ I) = (q : G ⧸ I) := hi
      have hout : (((q : G ⧸ I).out : G) : G ⧸ I) = (q : G ⧸ I) := QuotientGroup.out_eq' _
      have hm : ((i : G) * t a)⁻¹ * (q : G ⧸ I).out ∈ I := QuotientGroup.eq.1 (hqi.trans hout.symm)
      constructor
      · intro hK
        have h2 : ((i : G) * t a)⁻¹ * t b ∈ K := by
          have := K.mul_mem (h hm) hK
          simpa [mul_assoc] using this
        obtain ⟨hab, hI'⟩ := H a b i i.2 h2
        refine ⟨hab, Subtype.ext ?_⟩
        show (q : G ⧸ I) = ((t a : G) : G ⧸ I)
        rw [← hqi]
        exact QuotientGroup.eq.2 hI'
      · rintro ⟨rfl, rfl⟩
        have h3 : ((((⟨((t a : G) : G ⧸ I), MulAction.mem_orbit_self _⟩ :
            MulAction.orbit I ((t a : G) : G ⧸ I)) : G ⧸ I).out : G) : G ⧸ I) = ((t a : G) : G ⧸ I) :=
          QuotientGroup.out_eq' _
        exact h (QuotientGroup.eq.1 h3)
    simp only [hq]
    by_cases hab : a = b
    · subst hab
      simp [Finset.sum_ite_eq']
    · simp [hab]
  rw [linearIndependent_iff']
  intro s c hs i hi
  have hc := congrArg (fun z : HkAlg A I => ((z.1 (permRepBaseCosetVector A I) : fixd (permRep A I) I) :
    MonoidAlgebra A (G ⧸ I)).coeff ((t i : G) : G ⧸ I)) hs
  have key2 : ∀ a b, ((((hT A I (t a) : Module.End A (fixd (permRep A I) I)) (e.1 (permRepBaseCosetVector A I))) :
      fixd (permRep A I) I) : MonoidAlgebra A (G ⧸ I)).coeff ((t b : G) : G ⧸ I) = if a = b then 1 else 0 :=
    key
  simp [key2] at hc
  simpa [hi] using hc

end SlopeTestRemainingChoices

private theorem satInd_diag {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {x : kˣ} (hx : IsUnif x) {a b : Fin n → ℤ} {u : GL (Fin n) k} (hu : u ∈ unipB k (Fin n))
    (h : (pw x a)⁻¹ * u * pw x b ∈ KO k (Fin n)) : a ≤ b := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hx1 : valuation k (x : k) < 1 := by
    rw [← hpx]
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).1 hp.not_isUnit
  obtain ⟨g, hg⟩ := h
  intro i
  by_contra hlt
  have hlt' : b i < a i := lt_of_not_ge hlt
  have hent : (((pw x a)⁻¹ * u * pw x b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i =
      ((x ^ (b i - a i) : kˣ) : k) := by
    rw [Units.val_mul, Units.val_mul, pw, pw, ← map_inv, val_diagT, val_diagT, Matrix.mul_diagonal,
      Matrix.diagonal_mul, ((mem_unipB k).1 hu).2 i, mul_one, ← Units.val_mul, _root_.zpow_sub, mul_comm]
    rfl
  have hint : valuation k ((((pw x a)⁻¹ * u * pw x b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i) ≤ 1 := by
    rw [← hg]
    exact (g i i).2
  rw [hent] at hint
  obtain ⟨d, hd⟩ : ∃ d : ℕ, a i - b i = (d : ℤ) := ⟨(a i - b i).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hd0 : d ≠ 0 := by omega
  have hone : ((x ^ (b i - a i) : kˣ) : k) * (x : k) ^ d = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← hd, ← _root_.zpow_add]
    simp
  have hv := congrArg (valuation k) hone
  rw [map_one, map_mul, map_pow] at hv
  have hlt1 : valuation k (x : k) ^ d < 1 := pow_lt_one₀ zero_le' hx1 hd0
  have := mul_le_of_le_one_left (zero_le' : (0 : ValueGroupWithZero k) ≤ valuation k (x : k) ^ d) hint
  rw [hv] at this
  exact absurd (this.trans_lt hlt1) (lt_irrefl 1)

private theorem satInd_sep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {x : kˣ} (hx : IsUnif x) (hle : iwC k n ⊤ ≤ KO k (Fin n)) (a b : {a : Fin n → ℤ // Antitone a})
    (i : GL (Fin n) k) (hi : i ∈ iwC k n ⊤) (hK : (i * pw x a.1)⁻¹ * pw x b.1 ∈ KO k (Fin n)) :
    a = b ∧ (i * pw x a.1)⁻¹ * pw x a.1 ∈ iwC k n ⊤ := by
  have hx' := hx
  obtain ⟨p, hp, hpx⟩ := hx'
  have hx1 : valuation k (x : k) < 1 := by
    rw [← hpx]
    exact (Valuation.Integer.not_isUnit_iff_valuation_lt_one).1 hp.not_isUnit
  have hx0 : (0 : ValueGroupWithZero k) < valuation k (x : k) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 x.ne_zero)
  obtain ⟨F, hU, hM, hL, hUI, hLI, hF⟩ := factTorus k n ⊤
  have dom : ∀ c : {a : Fin n → ℤ // Antitone a}, Dom (fun j => x ^ c.1 j) := by
    intro c i j hij
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
    exact zpow_le_zpow_right_of_le_one₀ hx0 hx1.le (c.2 hij)
  have step : ∀ (c d : {a : Fin n → ℤ // Antitone a}) (u m l : GL (Fin n) k),
      u ∈ F.Uf ⊓ iwC k n ⊤ → m ∈ F.Mf ⊓ iwC k n ⊤ → l ∈ F.Lf ⊓ iwC k n ⊤ →
      (pw x c.1)⁻¹ * (u * m * l) * pw x d.1 ∈ KO k (Fin n) →
      (pw x c.1)⁻¹ * u * pw x d.1 ∈ KO k (Fin n) := by
    intro c d u m l hu hm hl hK'
    have h1 : (pw x d.1)⁻¹ * m * pw x d.1 ∈ KO k (Fin n) := hle ((hF _).1 m hm).2
    have h2 : (pw x d.1)⁻¹ * l * pw x d.1 ∈ KO k (Fin n) := hle (((hF _).2 (dom d)).2.2 l hl)
    have e : (pw x c.1)⁻¹ * u * pw x d.1 =
        ((pw x c.1)⁻¹ * (u * m * l) * pw x d.1) * ((pw x d.1)⁻¹ * l * pw x d.1)⁻¹ *
          ((pw x d.1)⁻¹ * m * pw x d.1)⁻¹ := by
      group
    rw [e]
    exact (KO k (Fin n)).mul_mem ((KO k (Fin n)).mul_mem hK' ((KO k (Fin n)).inv_mem h2))
      ((KO k (Fin n)).inv_mem h1)
  obtain ⟨u, hu, m, hm, l, hl, hiu⟩ := F.fact _ ((iwC k n ⊤).inv_mem hi)
  obtain ⟨u', hu', m', hm', l', hl', hiu'⟩ := F.fact _ hi
  have hK1 : (pw x a.1)⁻¹ * (u * m * l) * pw x b.1 ∈ KO k (Fin n) := by
    rw [← hiu]
    simpa [mul_assoc] using hK
  have hK2 : (pw x b.1)⁻¹ * (u' * m' * l') * pw x a.1 ∈ KO k (Fin n) := by
    rw [← hiu']
    have := (KO k (Fin n)).inv_mem hK
    simpa [mul_assoc] using this
  have hUb : ∀ v, v ∈ F.Uf → v ∈ unipB k (Fin n) := fun v hv => hU ▸ hv
  have hab : a.1 ≤ b.1 := satInd_diag hx (hUb u hu.1) (step a b u m l hu hm hl hK1)
  have hba : b.1 ≤ a.1 := satInd_diag hx (hUb u' hu'.1) (step b a u' m' l' hu' hm' hl' hK2)
  obtain rfl : a = b := Subtype.ext (le_antisymm hab hba)
  refine ⟨rfl, ?_⟩
  have hu1 : (pw x a.1)⁻¹ * u * pw x a.1 ∈ KO k (Fin n) := step a a u m l hu hm hl hK1
  have huU : (pw x a.1)⁻¹ * u * pw x a.1 ∈ F.Uf := by
    have := F.M_U _ (F.Mf.inv_mem ((hF _).2 (dom a)).1) u hu.1
    rw [inv_inv] at this
    exact this
  have huI : (pw x a.1)⁻¹ * u * pw x a.1 ∈ iwC k n ⊤ := by
    have hmem : (pw x a.1)⁻¹ * u * pw x a.1 ∈ unipO k n := ⟨hUb _ huU, hu1⟩
    rw [← hUI] at hmem
    exact hmem.2
  have e : (i * pw x a.1)⁻¹ * pw x a.1 =
      ((pw x a.1)⁻¹ * u * pw x a.1) * ((pw x a.1)⁻¹ * m * pw x a.1) * ((pw x a.1)⁻¹ * l * pw x a.1) := by
    rw [_root_.mul_inv_rev, hiu]
    group
  rw [e]
  exact (iwC k n ⊤).mul_mem ((iwC k n ⊤).mul_mem huI ((hF _).1 m hm).2) (((hF _).2 (dom a)).2.2 l hl)

private theorem satInd_gen {A G : Type} [CommRing A] [Group G] {I K : Subgroup G} (h : I ≤ K) (hI : HeckePair I)
    {κ : Type} [Fintype κ] (w : κ → G) (hw : ∀ i, w i ∈ K)
    (hw' : ∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) {ι : Type} (t : ι → G)
    (H : ∀ a b, ∀ i ∈ I, (i * t a)⁻¹ * t b ∈ K → a = b ∧ (i * t a)⁻¹ * t a ∈ I) :
    LinearIndependent A fun a => hT A I (t a) * ∑ i, hT A I (w i) := by
  obtain ⟨hf, hsum, -⟩ := hkTrace A G _ (permRep A I) I K h κ w hI hw hw'
  refine satInd_abs h hI hf (∑ i, hT A I (w i)) ?_ t H
  rw [← hsum]
  exact AddSubmonoidClass.coe_finset_sum _ _

theorem UpperTheory.V.AlgebraTools.satakeIndep :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A] (x : kˣ), IsUnif x → LinearIndependent A fun a : {a : Fin n → ℤ // Antitone a} => hT A (iwC k n ⊤) (pw x a.1) * ∑ w : Equiv.Perm (Fin n), hT A (iwC k n ⊤) (pm k n w) := by
  intro k _ _ _ _ n A _ x hx
  have hIw : iwC k n ⊤ = iwahori k (Fin n) := (memIwC k n ⊤).2.1
  have hle : iwC k n ⊤ ≤ KO k (Fin n) := by
    rw [hIw]
    exact iwahori_le_KO k (Fin n)
  have hbr := bruhatKO k n
  have hw' : ∀ g ∈ KO k (Fin n), ∃! w : Equiv.Perm (Fin n), ∃ a ∈ iwC k n ⊤, ∃ b ∈ iwC k n ⊤,
      g = a * pm k n w * b := by
    rw [hIw]
    exact hbr.2
  have hsep : ∀ (a b : {a : Fin n → ℤ // Antitone a}), ∀ i ∈ iwC k n ⊤,
      (i * pw x a.1)⁻¹ * pw x b.1 ∈ KO k (Fin n) → a = b ∧ (i * pw x a.1)⁻¹ * pw x a.1 ∈ iwC k n ⊤ :=
    fun a b i hi hK => satInd_sep hx hle a b i hi hK
  exact satInd_gen (A := A) (I := iwC k n ⊤) (K := KO k (Fin n)) hle (heckePairIwC k n ⊤).1
    (pm k n) hbr.1 hw' (fun a : {a : Fin n → ℤ // Antitone a} => pw x a.1) hsep
