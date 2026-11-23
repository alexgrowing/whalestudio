import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.KillLiftSingle
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingleAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SubEqZeroIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Points
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PermOf

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

noncomputable section

namespace UpperTheory.ConvolutionTheory.Ci

open PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory.FX

private theorem ke_esymm_map {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (s : Multiset R) (k : ℕ) :
    f (s.esymm k) = (s.map f).esymm k := by
  simp only [Multiset.esymm, map_multiset_sum, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def,
    map_multiset_prod]

private theorem ke_ext {n : ℕ} (s t : Multiset ℂ) (hs : s.card = n) (ht : t.card = n)
    (h : ∀ i : Fin n, s.esymm (i + 1) = t.esymm (i + 1)) : s = t := by
  have he : ∀ k, k ≤ n → s.esymm k = t.esymm k := by
    intro k hk
    rcases k with _ | k
    · simp [Multiset.esymm]
    · exact h ⟨k, hk⟩
  have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod
      = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [he j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  have := congrArg Polynomial.roots hp
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

private theorem ke_perm {n : ℕ} (x y : Fin n → ℂ) (h : Finset.univ.val.map x = Finset.univ.val.map y) :
    ∃ w : Equiv.Perm (Fin n), y = x ∘ w := by
  refine (perm_of_esymm n x y).1 fun i => ?_
  have e : ∀ z : Fin n → ℂ, eval z (esymm (Fin n) ℂ (i + 1)) = (Finset.univ.val.map z).esymm (i + 1) := fun z =>
    MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℂ (i + 1) z
  rw [e, e, h]

private theorem ke_evK_ren {ι κ : Type} [Fintype ι] [DecidableEq ι] (δ : ι → ι) (Λ : ι → ℂ) (h : κ → ℂ)
    (G : KF ι κ) : evK Λ h (map (ren δ) G) = evK (Λ ∘ δ) h G := by
  have : (ev Λ).comp (ren δ) = ev (Λ ∘ δ) := RingHom.ext fun f => by
    rw [RingHom.comp_apply, ren, (subst ι ι _ _ f).1]
    congr 2
    funext i
    simp [apply_ite]
  rw [evK, evK, coe_eval₂Hom, coe_eval₂Hom, eval₂_map, this]

private theorem ke_enum {n r : ℕ} (d : Fin r → ℕ) (hd : ∀ i, 0 < d i) (hs : ∑ i, d i = n) :
    ∃ blk : Fin n → Fin r, Function.Surjective blk ∧ ∀ M : Fin r → Multiset ℂ, (∀ i, (M i).card = d i) →
      ∃ x : Fin n → ℂ, ∀ g : Fin r → ℂ → ℂ, ∑ i, (M i).map (g i) = Finset.univ.val.map fun a => g (blk a) (x a) := by
  subst hs
  let e : (Σ i, Fin (d i)) ≃ Fin (∑ i, d i) := finSigmaFinEquiv
  refine ⟨fun a => (e.symm a).1, fun l => ⟨e ⟨l, ⟨0, hd l⟩⟩, by simp⟩, fun M hM => ?_⟩
  have h1 : ∀ i, ∃ y : Fin (d i) → ℂ, M i = Finset.univ.val.map y := by
    intro i
    have := hM i
    induction' h : M i using Quotient.inductionOn with l
    rw [h] at this
    have hl : l.length = d i := this
    refine ⟨fun a => l.get (a.cast hl.symm), ?_⟩
    rw [Fin.univ_val_map]
    congr 1
    apply List.ext_get (by simp [hl])
    intro k h1 h2
    simp
  choose y hy using h1
  refine ⟨fun a => y (e.symm a).1 (e.symm a).2, fun g => ?_⟩
  have h2 : (Finset.univ.val.map fun a => g (e.symm a).1 (y (e.symm a).1 (e.symm a).2)) =
      Finset.univ.val.map fun p : (Σ i, Fin (d i)) => g p.1 (y p.1 p.2) := by
    rw [← Multiset.map_univ_val_equiv e.symm, Multiset.map_map]
    rfl
  have h3 : ∀ (α : Type) [Fintype α] (f : α → ℂ), Finset.univ.val.map f = ∑ a, {f a} := by
    intro α _ f
    rw [← Finset.sum_multiset_singleton, ← Multiset.coe_mapAddMonoidHom, map_sum]
    simp
  rw [h2, h3, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy, Multiset.map_map, h3]
  rfl

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private structure AF (K : Type) [Field K] [NumberField K] (n : ℕ) where
  r : ℕ
  blk : Fin n → Fin r
  surj : Function.Surjective blk
  Λ : Ix K n → ℂ
  β : Pl K × Fin n → ℂ
  c : Pl K → ℝ

private def AF.Pt (a : AF K n) (S : Set (Pl K)) (M : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) : Prop :=
  ∃ lam : Fin a.r → ℂ, (∀ τ, M τ = Finset.univ.val.map fun i => a.Λ (τ, i) + lam (a.blk i)) ∧
    ∀ w ∉ S, t w = Finset.univ.val.map fun i => a.β (w, i) * Complex.exp (a.c w * lam (a.blk i))

private theorem ke_datum [IsTotallyComplex K] (hP : ParEx) (S : Set (Pl K)) (b : Datum K n) (hb : ∃ Λ t, b.Pt S Λ t) :
    ∃ a : AF K n, ∀ Λ t, b.Pt S Λ t ↔ a.Pt S Λ t := by
  classical
  obtain ⟨-, -, -, m, B, hAt, -⟩ := hb
  obtain ⟨blk, hsurj, hblk⟩ := ke_enum b.d b.pos b.sum
  choose x hx using fun τ => hblk (fun i => m i τ) fun i => ((hAt i).1 τ).1
  have hB : ∀ w, ∃ y : Fin n → ℂ, w ∉ S → ∀ g : Fin b.r → ℂ → ℂ,
      ∑ i, (B i w).map (g i) = Finset.univ.val.map fun a => g (blk a) (y a) := by
    intro w
    by_cases hw : w ∈ S
    · exact ⟨0, fun h => absurd hw h⟩
    · obtain ⟨y, hy⟩ := hblk (fun i => B i w) fun i => ((hAt i).2 w hw).1
      exact ⟨y, fun _ => hy⟩
  choose y hy using hB
  have hq : ∀ (w : Pl K) (z : ℂ), (Ideal.absNorm w.asIdeal : ℂ) ^ (-z) =
      Complex.exp (((-Real.log (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) * z) := by
    intro w z
    have : (Ideal.absNorm w.asIdeal : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    rw [Complex.cpow_def_of_ne_zero this, Complex.ofReal_neg, Complex.natCast_log]
    congr 1
    ring
  refine ⟨⟨b.r, blk, hsurj, fun p => x p.1 p.2, fun p => y p.1 p.2, fun w => -Real.log (Ideal.absNorm w.asIdeal)⟩,
    fun Λ t => ⟨?_, ?_⟩⟩
  · rintro ⟨lam, m', B', hAt', h1, h2⟩
    have hm : ∀ i τ, m' i τ = m i τ := fun i τ =>
      ((hP K (b.d i) (b.pos i) (b.μ i) (b.V i) (b.summand i)).1 τ).unique ((hAt' i).1 τ) ((hAt i).1 τ)
    have hB : ∀ i, ∀ w ∉ S, B' i w = B i w := fun i w hw =>
      ((hP K (b.d i) (b.pos i) (b.μ i) (b.V i) (b.summand i)).2.1 w ((hAt i).2 w hw).2.1).unique
        ((hAt' i).2 w hw) ((hAt i).2 w hw)
    refine ⟨lam, fun τ => ?_, fun w hw => ?_⟩
    · rw [h1]
      simp only [hm]
      exact hx τ fun i z => z + lam i
    · rw [h2 w hw]
      simp only [hB _ w hw, hq]
      exact hy w hw fun i z => z * Complex.exp (_ * lam i)
  · rintro ⟨lam, h1, h2⟩
    refine ⟨lam, m, B, hAt, fun τ => ?_, fun w hw => ?_⟩
    · rw [h1]
      exact (hx τ fun i z => z + lam i).symm
    · rw [h2 w hw]
      simp only [hq]
      exact (hy w hw fun i z => z * Complex.exp (_ * lam i)).symm

private theorem ke_bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (SE : Set (Pl E)) (SF : Set (Pl F)) (hS : ∀ w : Pl E, w ∈ SE ↔ w.under (𝓞 F) ∈ SF) (a : AF F n) :
    ∃ a' : AF E n, ∀ Λ t, a'.Pt SE Λ t ↔ ∃ Λ' t', a.Pt SF Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ w ∉ SE, t w = bcSat t' w := by
  refine ⟨⟨a.r, a.blk, a.surj, fun p => a.Λ (p.1.comp (algebraMap F E), p.2),
    fun p => a.β (p.1.under (𝓞 F), p.2) ^ resDeg F p.1, fun w => resDeg F w * a.c (w.under (𝓞 F))⟩, fun Λ t => ?_⟩
  have key : ∀ (lam : Fin a.r → ℂ) (w : Pl E),
      (Finset.univ.val.map fun i => a.β (w.under (𝓞 F), i) * Complex.exp (a.c (w.under (𝓞 F)) * lam (a.blk i))).map
        (· ^ resDeg F w) = Finset.univ.val.map fun i => a.β (w.under (𝓞 F), i) ^ resDeg F w *
          Complex.exp (((resDeg F w * a.c (w.under (𝓞 F)) : ℝ) : ℂ) * lam (a.blk i)) := by
    intro lam w
    rw [Multiset.map_map]
    congr 1
    funext i
    rw [Function.comp_apply, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    rw [mul_assoc]
  constructor
  · rintro ⟨lam, h1, h2⟩
    refine ⟨_, _, ⟨lam, fun _ => rfl, fun _ _ => rfl⟩, funext h1, fun w hw => ?_⟩
    rw [h2 w hw, bcSat, key]
  · rintro ⟨Λ', t', ⟨lam, h1, h2⟩, rfl, h3⟩
    refine ⟨lam, fun τ => h1 _, fun w hw => ?_⟩
    rw [h3 w hw, bcSat, h2 _ (fun h => hw ((hS w).2 h)), key]

private def blkW (K : Type) [Field K] (n : ℕ) : Subgroup (Equiv.Perm (Ix K n)) where
  carrier := {σ | ∃ w : (K →+* ℂ) → Equiv.Perm (Fin n), σ = Equiv.prodCongrRight w}
  one_mem' := ⟨1, by ext <;> simp⟩
  mul_mem' := by
    rintro _ _ ⟨w, rfl⟩ ⟨w', rfl⟩
    exact ⟨w * w', by ext ⟨a, b⟩ <;> simp⟩
  inv_mem' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨w⁻¹, rfl⟩

private theorem ke_ms (L : Ix K n → ℂ) (w : (K →+* ℂ) → Equiv.Perm (Fin n)) :
    msOf (L ∘ Equiv.prodCongrRight w) = msOf L := by
  funext τ
  rw [msOf, msOf]
  conv_rhs => rw [← Multiset.map_univ_val_equiv (w τ), Multiset.map_map]
  rfl

private theorem ke_fam (S : Set (Pl K)) (a : AF K n) :
    ∃ b : Fam (Ix K n) {x : Pl K × Fin n // x.1 ∉ S}, ∀ (L : Ix K n → ℂ) (t : Pl K → Multiset ℂ),
      (a.Pt S (msOf L) t → ∃ σ ∈ blkW K n, b.Mem (L ∘ σ) fun x => hval t x.1) ∧
      ((∀ w ∉ S, (t w).card = n) → ∀ σ ∈ blkW K n, b.Mem (L ∘ σ) (fun x => hval t x.1) → a.Pt S (msOf L) t) := by
  classical
  obtain ⟨τ₀⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨sec, hsec⟩ := a.surj.hasRightInverse
  let b : Fam (Ix K n) {x : Pl K × Fin n // x.1 ∉ S} :=
    { r := a.r
      Λ := a.Λ
      emb := Matrix.of fun x l => if a.blk x.2 = l then 1 else 0
      pr := Matrix.of fun l x => if x = (τ₀, sec l) then 1 else 0
      pr_emb := by
        ext l l'
        rw [Matrix.mul_apply, Finset.sum_eq_single (τ₀, sec l)]
        · simp [hsec l, Matrix.one_apply]
        · intro x _ hx
          simp [hx]
        · simp
      h := fun x => (Finset.univ.val.map fun i => (AddMonoidAlgebra.single
        (fun l => if a.blk i = l then a.c x.1.1 else 0) (C (a.β (x.1.1, i))) : EP (Fin a.r))).esymm (x.1.2 + 1) }
  have h1 : ∀ (lam : Fin a.r → ℂ) (x : Ix K n), ∑ j, (b.emb x j : ℂ) * lam j = lam (a.blk x.2) := by
    intro lam x
    simp [b, apply_ite]
  have h2 : ∀ (lam : Fin a.r → ℂ) x, ev lam (b.h x) = (Finset.univ.val.map fun i =>
      a.β (x.1.1, i) * Complex.exp (a.c x.1.1 * lam (a.blk i))).esymm (x.1.2 + 1) := by
    intro lam x
    rw [ke_esymm_map, Multiset.map_map]
    congr 2
    funext i
    simp [ev, PositivityTheory.Rg.Fx.lift, expChar, apply_ite]
  refine ⟨b, fun L t => ⟨?_, ?_⟩⟩
  · rintro ⟨lam, hL, ht⟩
    choose w hw using fun τ => ke_perm _ _ (hL τ)
    refine ⟨_, ⟨w, rfl⟩, lam, fun x => ?_, fun x => ?_⟩
    · rw [h1]
      exact (congrFun (hw x.1) x.2).symm
    · rw [h2, ← ht _ x.2]
      rfl
  · rintro hc _ ⟨w, rfl⟩ ⟨lam, hL, ht⟩
    refine ⟨lam, fun τ => ?_, fun v hv => ?_⟩
    · rw [← ke_ms L w, msOf]
      congr 1
      funext i
      rw [hL, h1]
    · refine ke_ext _ _ (hc v hv) (by simp) fun i => ?_
      exact (ht ⟨(v, i), hv⟩).trans (h2 _ _)

private theorem ke_main (S : Set (Pl K)) (B : Type) [Fintype B] (a : B → AF K n) (L : Ix K n → ℂ)
    (t : Pl K → Multiset ℂ) (hc : ∀ w ∉ S, (t w).card = n) (h : ∀ i, ¬ (a i).Pt S (msOf L) t) :
    ∃ Φ : KF (Ix K n) (Pl K × Fin n), admitted S Φ ∧ evK L (hval t) Φ ≠ 0 ∧
      ∀ i L' t', (a i).Pt S (msOf L') t' → evK L' (hval t') Φ = 0 := by
  classical
  choose b hb using fun i => ke_fam S (a i)
  obtain ⟨G, hG1, hG2, hG3⟩ := killing0 _ _ B (blkW K n) b L (fun x => hval t x.1)
    fun σ hσ i hm => h i ((hb i L t).2 hc σ hσ hm)
  have hr : ∀ (L' : Ix K n → ℂ) (h' : Pl K × Fin n → ℂ),
      evK L' h' (rename Subtype.val G) = evK L' (fun x => h' x.1) G := by
    intro L' h'
    rw [evK, evK, coe_eval₂Hom, coe_eval₂Hom, eval₂_rename]
    rfl
  refine ⟨rename Subtype.val G, ⟨fun w => ?_, fun x hx => ?_⟩, by rwa [hr], fun i L' t' hp => ?_⟩
  · rw [map_rename]
    have h0 := hG1 (Equiv.prodCongrRight w) ⟨w, rfl⟩
    have h1 : (Equiv.prodCongrRight w : Ix K n → Ix K n) = fun x => (x.1, w x.1 x.2) := rfl
    rw [h1] at h0
    rw [h0]
  · obtain ⟨y, -, rfl⟩ := mem_vars_rename _ _ hx
    exact y.2
  · obtain ⟨σ, hσ, hm⟩ := (hb i L' t').1 hp
    rw [hr, ← hG1 σ hσ, ke_evK_ren]
    exact (sub_eq_zero_iff _ _ _ _).1 (hG2 i) _ _ hm

theorem killEx_listed (hP : ParEx)
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (n : ℕ) (SE : Set (Pl E)) (SF : Set (Pl F)) (hS : ∀ w : Pl E, w ∈ SE ↔ w.under (𝓞 F) ∈ SF)
    (B B' : Type) [Fintype B] [Fintype B'] (b : B → Datum E n) (b' : B' → Datum F n)
    (hb : ∀ i, ∃ Λ t, (b i).Pt SE Λ t) (hb' : ∀ i, ∃ Λ t, (b' i).Pt SF Λ t)
    (L : Ix E n → ℂ) (t : Pl E → Multiset ℂ) (hc : ∀ w ∉ SE, (t w).card = n) (h : ∀ i, ¬ (b i).Pt SE (msOf L) t)
    (h' : ∀ i Λ' t', (b' i).Pt SF Λ' t' → ¬ (msOf L = bcInf Λ' ∧ ∀ w ∉ SE, t w = bcSat t' w)) :
    ∃ Φ : KF (Ix E n) (Pl E × Fin n), admitted SE Φ ∧ evK L (hval t) Φ ≠ 0 ∧ (∀ i, Kills SE Φ (b i)) ∧
      ∀ i (L' : Ix F n → ℂ) t', (b' i).Pt SF (msOf L') t' →
        evK (fun y : Ix E n => L' (y.1.comp (algebraMap F E), y.2)) (hval (bcSat t')) Φ = 0 := by
  choose a ha using fun i => ke_datum hP SE (b i) (hb i)
  choose a' ha' using fun i => ke_datum hP SF (b' i) (hb' i)
  choose a'' ha'' using fun i => ke_bc SE SF hS (a' i)
  obtain ⟨Φ, h1, h2, h3⟩ := ke_main SE (B ⊕ B') (Sum.elim a a'') L t hc (by
    rintro (i | i) hp
    · exact h i ((ha i _ _).2 hp)
    · obtain ⟨Λ', t', hp', he⟩ := (ha'' i _ _).1 hp
      exact h' i Λ' t' ((ha' i _ _).2 hp') he)
  refine ⟨Φ, h1, h2, fun i L' t' hp => h3 (Sum.inl i) L' t' ((ha i _ _).1 hp), fun i L' t' hp => ?_⟩
  exact h3 (Sum.inr i) _ _ ((ha'' i _ _).2 ⟨_, t', (ha' i _ _).1 hp, rfl, fun _ _ => rfl⟩)

end UpperTheory.ConvolutionTheory.Ci

theorem UpperTheory.ConvolutionTheory.Ci.killEx :
    ParEx → KillEx := by
  intro hP F E _ _ _ _ _ _ _ n SE SF hS B B' _ _ b b' hb hb' L t hc hO
  exact killEx_listed hP F E n SE SF hS B B' b b' hb hb' L t hc (fun i => hO.1 _) fun i => hO.2 _
