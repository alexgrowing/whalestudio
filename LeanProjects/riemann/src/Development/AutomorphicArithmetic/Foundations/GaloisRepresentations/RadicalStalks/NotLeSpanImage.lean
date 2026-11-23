import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private lemma not_le_span_image {k P : Type*} [Field k] [AddCommGroup P] [Module k P] [FiniteDimensional k P]
    (G : Submodule k P) (A : P →+ P) (q : ℕ) (hq : 0 < q) (hA : ∀ (l : k) x, A (l • x) = l ^ q • A x)
    (v : P) (hv : v ∈ G) (hv0 : v ≠ 0) (hAv : A v = 0) :
    ¬ G ≤ Submodule.span k (A '' G) := by
  intro hle
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual k P, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff k v).1 h)
  let K : Submodule k P := G ⊓ LinearMap.ker ℓ
  have hKG : K < G := by
    refine lt_of_le_of_ne inf_le_left fun h => hℓ ?_
    have : v ∈ K := h ▸ hv
    exact this.2
  let b := Module.finBasis k K
  let t : Fin (Module.finrank k K) → P := fun i => A (b i : P)
  have hAK : ∀ y ∈ K, A y ∈ Submodule.span k (Set.range t) := by
    intro y hy
    have e : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : P) := by
      have h : ((∑ i, b.repr ⟨y, hy⟩ i • b i : K) : P) = y := by rw [b.sum_repr]
      rw [Submodule.coe_sum] at h
      simpa only [Submodule.coe_smul] using h.symm
    rw [e, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span k (A '' G) ≤ Submodule.span k (Set.range t) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    let l : k := ℓ g / ℓ v
    have hy : g - l • v ∈ K := by
      refine ⟨G.sub_mem hg (G.smul_mem _ hv), ?_⟩
      simp [l, hℓ]
    have e : A g = A (g - l • v) := by
      rw [map_sub, hA, hAv, smul_zero, sub_zero]
    rw [SetLike.mem_coe, e]
    exact hAK _ hy
  have h1 : Module.finrank k G ≤ Module.finrank k (Submodule.span k (Set.range t)) :=
    Submodule.finrank_mono (hle.trans hspan)
  have h2 : Module.finrank k (Submodule.span k (Set.range t)) ≤ Module.finrank k K := by
    have := finrank_range_le_card (R := k) t
    simpa [Set.finrank] using this
  have h3 := Submodule.finrank_lt_finrank_of_lt hKG
  omega

private lemma sub_smul_pow (p : ℕ) [Fact p.Prime] {k P : Type*} [Field k] [CharP k p] [AddCommGroup P] [Module k P]
    (T : Module.End k P) (l : k) (n : ℕ) : (T - l • 1) ^ (p ^ n) = T ^ (p ^ n) - (l ^ (p ^ n)) • 1 := by
  have h : ((Polynomial.X - Polynomial.C l) ^ (p ^ n) : Polynomial k) =
      Polynomial.X ^ (p ^ n) - Polynomial.C (l ^ (p ^ n)) := by
    rw [sub_pow_char_pow, Polynomial.C_pow]
  have := congrArg (Polynomial.aeval T) h
  simpa [Algebra.algebraMap_eq_smul_one, smul_pow] using this

private lemma pow_card_subring {k : Type*} [Field k] (R : Subring k) [Finite R] (x : R) : x ^ Nat.card R = x := by
  classical
  letI := Fintype.ofFinite R
  letI : Field R := Fintype.fieldOfDomain R
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

private lemma eig_of_gen (p : ℕ) [Fact p.Prime] {k P : Type*} [Field k] [CharP k p] [AddCommGroup P] [Module k P]
    (T : Module.End k P) (l : k) (f : ℕ) (hf : 0 < f) (hl : l ^ (p ^ f) = l) (y : P)
    (hy : y ∈ T.maxGenEigenspace l) (hT : (T ^ (p ^ f)) y = T y) : T y = l • y := by
  obtain ⟨n, hn⟩ := Module.End.mem_maxGenEigenspace _ _ _ |>.1 hy
  set N : Module.End k P := T - l • 1 with hN
  have hq : 2 ≤ p ^ f := by
    calc 2 ≤ p := (Fact.out : p.Prime).two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf
  have hNq : (N ^ (p ^ f)) y = N y := by
    rw [hN, sub_smul_pow p, hl]
    simp [hT]
  have hit : ∀ j : ℕ, (N ^ (j * (p ^ f - 1) + 1)) y = N y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (j + 1) * (p ^ f - 1) + 1 = j * (p ^ f - 1) + p ^ f := by
        have : p ^ f - 1 + 1 = p ^ f := by omega
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc, this]
      rw [e, pow_add, Module.End.mul_apply, hNq, ← Module.End.mul_apply, ← pow_succ, ih]
  have hz : N y = 0 := by
    rw [← hit n]
    have e : n * (p ^ f - 1) + 1 = (n * (p ^ f - 1) + 1 - n) + n := by
      have : n ≤ n * (p ^ f - 1) := Nat.le_mul_of_pos_right n (by omega)
      omega
    rw [e, pow_add, Module.End.mul_apply, hn, map_zero]
  have : T y - l • y = 0 := by simpa [hN] using hz
  exact sub_eq_zero.1 this

private lemma exists_not_mem {k C P : Type*} [Field k] [IsAlgClosed k] [CommRing C] [AddCommGroup P] [Module k P]
    [FiniteDimensional k P] (ρ : C →+* Module.End k P) (χ : C →+* k) (q : ℕ) (hq : 0 < q) (A : P →+ P)
    (hsemi : ∀ (l : k) x, A (l • x) = l ^ q • A x) (hcomm : ∀ c x, A (ρ c x) = ρ c (A x))
    (hfix : ∀ c, χ c ^ q = χ c) (hinj : Function.Injective fun x : k => x ^ q) (ε a g : C)
    (hε : ρ ε * ρ ε = ρ ε) (hε1 : χ ε = 1) (hnil : ∃ e : ℕ, ρ a ^ e * ρ ε = 0)
    (annG : ∀ x, ρ g x = 0 → ∃ u v, x = ρ a u + ρ (1 - ε) v)
    (v : P) (hv0 : v ≠ 0) (hv : ∀ c, ρ c v = χ c • v) (hAv : A v = 0) :
    ∃ u ∈ ⨅ c, (ρ c).maxGenEigenspace (χ c), ρ g u ∉ (Submodule.span k (Set.range A)).map (ρ g) := by
  classical
  let U : (C → k) → Submodule k P := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  let G : Submodule k P := U χ
  let H : Submodule k P := ⨆ ψ : {ψ : C → k // ψ ≠ χ}, U ψ
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j m0, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace m0) ((ρ j).maxGenEigenspace m0) :=
    fun i j m0 => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) m0
  have hind : iSupIndep U :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun x => ρ x) hmaps
  have htop : ⨆ ψ, U ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun x => ρ x) hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (ρ i))
  have hUH : ∀ ψ : C → k, ψ ≠ χ → U ψ ≤ H := fun ψ h =>
    le_iSup (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) ⟨ψ, h⟩
  have hsup : G ⊔ H = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun ψ => ?_
    by_cases h : ψ = χ
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (hUH ψ h)
  have hdisj : Disjoint G H :=
    (hind χ).mono_right (iSup_le fun ψ => le_iSup₂_of_le (f := fun j (_ : j ≠ ⇑χ) => U j) ψ.1 ψ.2 le_rfl)
  have hρU : ∀ c ψ, ∀ x ∈ U ψ, ρ c x ∈ U ψ := by
    intro c ψ x hx
    simp only [U, Submodule.mem_iInf] at hx ⊢
    exact fun d => hmaps c d _ (hx d)
  have hρH : ∀ c, ∀ x ∈ H, ρ c x ∈ H := by
    intro c x hx
    have hle : H ≤ H.comap (ρ c) := iSup_le fun ψ y hy => hUH ψ.1 ψ.2 (hρU c ψ.1 y hy)
    exact hle hx
  have hAU : ∀ ψ : C → k, ∀ x ∈ U ψ, A x ∈ U (fun c => ψ c ^ q) := by
    intro ψ x hx
    simp only [U, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace] at hx ⊢
    intro d
    obtain ⟨n, hn⟩ := hx d
    refine ⟨n, ?_⟩
    have step : ∀ (n : ℕ) y, ((ρ d - (ψ d ^ q) • 1) ^ n) (A y) = A (((ρ d - ψ d • 1) ^ n) y) := by
      intro n
      induction n with
      | zero => intro y; simp
      | succ n ih =>
        intro y
        have e : (ρ d - (ψ d ^ q) • 1) (A y) = A ((ρ d - ψ d • 1) y) := by
          simp [hcomm, hsemi, map_sub]
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, e, ih]
    rw [step, hn, map_zero]
  have hAG : ∀ x ∈ G, A x ∈ G := by
    intro x hx
    have := hAU χ x hx
    have e : (fun c => χ c ^ q) = ⇑χ := funext hfix
    rwa [e] at this
  have hAH : ∀ x ∈ H, A x ∈ H := by
    intro x hx
    refine Submodule.iSup_induction (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) (motive := fun x => A x ∈ H) hx ?_ ?_ ?_
    · intro ψ y hy
      refine hUH _ ?_ (hAU ψ.1 y hy)
      intro h
      refine ψ.2 (funext fun c => hinj ?_)
      show ψ.1 c ^ q = χ c ^ q
      rw [hfix, ← congrFun h c]
    · simp
    · intro y z hy hz
      rw [map_add]
      exact H.add_mem hy hz
  have hεG : ∀ x ∈ G, ρ ε x = x := by
    have aux : ∀ (n : ℕ) (x : P), ((ρ ε - (1 : k) • 1) ^ n) x = 0 → ρ ε x = x := by
      intro n
      induction n with
      | zero => intro x hx; simp at hx; simp [hx]
      | succ n ih =>
        intro x hx
        rw [pow_succ, Module.End.mul_apply] at hx
        have h1 := ih _ hx
        have h2 : ρ ε (ρ ε x) = ρ ε x := by rw [← Module.End.mul_apply, hε]
        simp only [one_smul, LinearMap.sub_apply, Module.End.one_apply, map_sub, h2, sub_self] at h1
        exact sub_eq_zero.1 h1.symm
    intro x hx
    have h := (Submodule.mem_iInf _).1 hx ε
    rw [hε1] at h
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 h
    exact aux n x hn
  have h1εG : ∀ x ∈ G, ρ (1 - ε) x = 0 := by
    intro x hx
    simp [map_sub, hεG x hx]
  let Wd : Submodule k P := Submodule.span k (A '' G)
  have hWG : Wd ≤ G := Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hAG x hx)
  have haW : ∀ x ∈ Wd, ρ a x ∈ Wd := by
    intro x hx
    have hle : Wd ≤ Wd.comap (ρ a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      show ρ a (A y) ∈ Wd
      rw [← hcomm]
      exact Submodule.subset_span ⟨_, hρU a χ y hy, rfl⟩
    exact hle hx
  have hvG : v ∈ G := by
    refine (Submodule.mem_iInf _).2 fun c => (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
    simp [hv]
  by_contra hno
  push_neg at hno
  have hS : Submodule.span k (Set.range A) ≤ Wd ⊔ H := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ G ⊔ H := hsup ▸ Submodule.mem_top
    obtain ⟨z1, h1, z2, h2, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z1, h1, rfl⟩) (hAH z2 h2)
  have hstep : ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + ρ a u' := by
    intro u hu
    obtain ⟨s, hs, hsu⟩ := (Submodule.mem_map).1 (hno u hu)
    obtain ⟨u', v', hx⟩ := annG (u - s) (by rw [map_sub, hsu, sub_self])
    obtain ⟨w, hw, h, hh, rfl⟩ := Submodule.mem_sup.1 (hS hs)
    have d : ∀ z : P, z ∈ G ⊔ H := fun z => hsup ▸ Submodule.mem_top
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Submodule.mem_sup.1 (d u')
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 (d v')
    have e0 : ρ (1 - ε) v1 = 0 := h1εG v1 hv1
    have e1 : u - w - ρ a u1 = h + ρ a u2 + ρ (1 - ε) v2 := by
      simp only [map_add, e0] at hx
      have h' := sub_eq_iff_eq_add.1 hx
      rw [h']
      abel
    have hd0 : u - w - ρ a u1 = 0 := by
      refine Submodule.disjoint_def.1 hdisj _ (G.sub_mem (G.sub_mem hu (hWG hw)) (hρU a _ u1 hu1)) ?_
      rw [e1]
      exact H.add_mem (H.add_mem hh (hρH a _ hu2)) (hρH _ _ hv2)
    refine ⟨w, hw, u1, hu1, ?_⟩
    have h' := sub_eq_zero.1 hd0
    exact sub_eq_iff_eq_add'.1 h'
  have hpow : ∀ (n : ℕ), ∀ x ∈ Wd, (ρ a ^ n) x ∈ Wd := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact haW _ (ih x hx)
  have hiter : ∀ (n : ℕ), ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + (ρ a ^ n) u' := by
    intro n
    induction n with
    | zero => intro u hu; exact ⟨0, Wd.zero_mem, u, hu, by simp⟩
    | succ n ih =>
      intro u hu
      obtain ⟨w, hw, u', hu', e⟩ := ih u hu
      obtain ⟨w2, hw2, u'', hu'', e2⟩ := hstep u' hu'
      refine ⟨w + (ρ a ^ n) w2, Wd.add_mem hw (hpow n _ hw2), u'', hu'', ?_⟩
      rw [pow_succ, Module.End.mul_apply, e, e2, map_add, add_assoc]
  obtain ⟨e, he⟩ := hnil
  have hGW : G ≤ Wd := by
    intro u hu
    obtain ⟨w, hw, u', hu', eq⟩ := hiter e u hu
    have h0 : (ρ a ^ e) u' = 0 := by
      have h1 : (ρ a ^ e * ρ ε) u' = 0 := by rw [he]; rfl
      rwa [Module.End.mul_apply, hεG u' hu'] at h1
    rw [eq, h0, add_zero]
    exact hw
  exact not_le_span_image G A q hq hsemi v hvG hv0 hAv hGW

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.alg2 :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ), 0 < f →
      Nat.card (C ⧸ w) = p ^ f → ∀ (π : Par p w f) (χ : C →+* k) (P : Type 1) [AddCommGroup P] [Module k P] (ρ : C → Module.End k P) (F : Submodule k P)
      (Φ : P →+ P), Lin p π χ ρ F Φ →
      ∃ x : Module.Dual k P, (∀ y, x (ρ π.ε y) = x y) ∧ (∀ z, x (ρ π.g (Φ^[f] z)) = 0) ∧ ∃ y, (∀ c, ρ c y = χ c • y) ∧ x y ≠ 0 := by
  intro p _ k _ _ _ C _ w f hf hcard π χ P _ _ ρ F Φ L
  haveI := L.fin
  let ρh : C →+* Module.End k P :=
    { toFun := ρ, map_one' := L.one, map_mul' := L.mul, map_add' := L.add
      map_zero' := by
        have h := L.add 0 0
        simpa using h }
  have hp : ρh (p : C) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap k (Module.End k P)), CharP.cast_eq_zero k p, map_zero]
  have hdvd : ∀ x : C, (p : C) ∣ x → ρh x = 0 := by
    rintro _ ⟨d, rfl⟩
    rw [map_mul, hp, zero_mul]
  have hfix : ∀ c, χ c ^ (p ^ f) = χ c := by
    have e : (C ⧸ w) ≃ χ.range :=
      ((Ideal.quotEquivOfEq L.ker.symm).trans (RingHom.quotientKerEquivRange χ)).toEquiv
    have hcard' : Nat.card χ.range = p ^ f := (Nat.card_congr e).symm.trans hcard
    haveI : Finite χ.range := Nat.finite_of_card_ne_zero (by
      rw [hcard']; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    intro c
    have h := pow_card_subring χ.range ⟨χ c, c, rfl⟩
    rw [hcard'] at h
    exact congrArg Subtype.val h
  have hinj : Function.Injective fun x : k => x ^ (p ^ f) := by
    intro x y h
    exact (iterateFrobenius k p f).injective (by simpa [iterateFrobenius_def] using h)
  let A : P →+ P :=
    { toFun := (⇑Φ)^[f], map_zero' := iterate_map_zero Φ f, map_add' := iterate_map_add Φ f }
  have hsemiN : ∀ (n : ℕ) (l : k) x, (⇑Φ)^[n] (l • x) = l ^ (p ^ n) • (⇑Φ)^[n] x := by
    intro n
    induction n with
    | zero => intro l x; simp
    | succ n ih =>
      intro l x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.semi, ← pow_mul, pow_succ]
  have hcommN : ∀ (n : ℕ) c x, (⇑Φ)^[n] (ρ c x) = ρ c ((⇑Φ)^[n] x) := by
    intro n
    induction n with
    | zero => intro c x; rfl
    | succ n ih =>
      intro c x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.comm]
  obtain ⟨x0, hx0F, hx0, -⟩ := L.line
  have hAv : A (ρ π.ε x0) = 0 := by
    show (⇑Φ)^[f] (ρ π.ε x0) = 0
    have e : (⇑Φ)^[f] (ρ π.ε x0) = (⇑Φ)^[f - 1] (Φ (ρ π.ε x0)) := by
      rw [← Function.iterate_succ_apply]
      congr 2
      omega
    rw [e, L.comm, (L.kerΦ x0).2 hx0F, map_zero, iterate_map_zero]
  have hε : ρh π.ε * ρh π.ε = ρh π.ε := by
    have h := hdvd _ π.idem
    rwa [map_sub, map_mul, sub_eq_zero] at h
  have hε1 : χ π.ε = 1 := by
    have h : π.ε - 1 ∈ RingHom.ker χ := L.ker ▸ π.one
    rwa [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h
  have hnil : ∃ e : ℕ, ρh π.a ^ e * ρh π.ε = 0 := by
    obtain ⟨e, he⟩ := π.nil
    refine ⟨e, ?_⟩
    have h := hdvd _ he
    rwa [map_mul, map_pow] at h
  obtain ⟨u, hu, hnot⟩ := exists_not_mem ρh χ (p ^ f) (pow_pos (Fact.out : p.Prime).pos f) A
    (fun l x => hsemiN f l x) (fun c x => hcommN f c x) hfix hinj π.ε π.a π.g hε hε1 hnil
    (fun x h => by
      obtain ⟨u, v, e⟩ := L.annG x h
      exact ⟨u, v, e⟩)
    (ρ π.ε x0) hx0 (fun c => L.eig c x0 hx0F) hAv
  have kills : ∀ x, χ x = 0 → ρh x (ρh π.g u) = 0 := by
    intro x hx
    have hxw : x ∈ w := L.ker ▸ (RingHom.mem_ker.2 hx)
    obtain ⟨u0, d1⟩ := π.gen x hxw
    have hd : (p : C) ∣ x * π.g := by
      have e : x * π.g = (π.ε * x - π.a * u0) * π.g - x * (π.ε * π.g - π.g) + u0 * (π.a * π.g) := by ring
      rw [e]
      exact dvd_add (dvd_sub (d1.mul_right _) (π.geps.mul_left _)) ((Dvd.intro _ π.prod.symm).mul_left _)
    have h := hdvd _ hd
    rw [map_mul] at h
    rw [← Module.End.mul_apply, h]
    rfl
  have eig : ∀ c, ρ c (ρ π.g u) = χ c • ρ π.g u := by
    intro c
    have hyG : ρh π.g u ∈ (ρh c).maxGenEigenspace (χ c) := by
      have hcm : Commute (ρh c) (ρh π.g) := by
        show ρh c * ρh π.g = ρh π.g * ρh c
        rw [← map_mul, ← map_mul, mul_comm]
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hcm _ ((Submodule.mem_iInf _).1 hu c)
    refine eig_of_gen p (ρh c) (χ c) f hf (hfix c) _ hyG ?_
    have hw : χ (c ^ (p ^ f) - c) = 0 := by rw [map_sub, map_pow, hfix, sub_self]
    have h := kills _ hw
    rwa [map_sub, map_pow, LinearMap.sub_apply, sub_eq_zero] at h
  obtain ⟨ξ, hξ1, hξ2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hεε : ∀ y, ρ π.ε (ρ π.ε y) = ρ π.ε y := fun y => by
    have h := congrArg (fun T : Module.End k P => T y) hε
    exact h
  have hεg : ∀ y, ρ π.ε (ρ π.g y) = ρ π.g y := fun y => by
    have h := hdvd _ π.geps
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact congrArg (fun T : Module.End k P => T y) h
  refine ⟨ξ ∘ₗ ρ π.ε, fun y => ?_, fun z => ?_, ρ π.g u, eig, ?_⟩
  · simp only [LinearMap.comp_apply, hεε]
  · simp only [LinearMap.comp_apply, hεg]
    have hm : ρh π.g (A z) ∈ (Submodule.span k (Set.range A)).map (ρh π.g) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨z, rfl⟩)
    have h := Submodule.mem_map_of_mem (f := ξ) hm
    rw [hξ2, Submodule.mem_bot] at h
    exact h
  · simp only [LinearMap.comp_apply, hεg]
    exact hξ1
