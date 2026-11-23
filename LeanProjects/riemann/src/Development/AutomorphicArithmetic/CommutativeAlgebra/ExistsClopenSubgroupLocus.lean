import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotGlobalHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackKernelOfKernelPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocusStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsMemUIdealIdempotentModPrimePow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

section ring
variable {p : ℕ} [Fact p.Prime] {D : Datum p}

private theorem mul_bar_eq (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) :
    ∃ z : 𝓞 D.F, (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - (r : 𝓞 D.F)) = (p : 𝓞 D.F) * z := by
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have e1 : ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) = (D.ω - r) * (D.bar D.ω - r) := by
    push_cast
    linear_combination r * htr - hnm
  have hcw : ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) ∈ w := by
    rw [e1]
    exact w.mul_mem_right (D.bar D.ω - r) (hu (sub_mem_uIdeal D r))
  have hpc : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hnd
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hnd
    refine hw ((Ideal.eq_top_iff_one w).2 ?_)
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
    rw [← h]
    exact w.add_mem (w.mul_mem_left _ (hu (p_mem_uIdeal D r))) (w.mul_mem_left _ hcw)
  obtain ⟨z, hz⟩ := hpc
  refine ⟨z, ?_⟩
  rw [← e1, hz]
  push_cast
  rfl

private theorem uIdeal_pow_le (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) (e : ℕ)
    (ε : 𝓞 D.F) (hε : ε ∈ uIdeal D r) (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1) :
    uIdeal D r ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e, ε} := by
  set I := Ideal.span {(p : 𝓞 D.F) ^ e, ε} with hI
  let π := Ideal.Quotient.mk I
  have hpe : π ((p : 𝓞 D.F) ^ e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_insert _ _))
  have hε0 : π ε = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hbar1 : π (D.bar ε) = 1 := by
    obtain ⟨d, hd⟩ := h1
    have e0 : D.bar ε = 1 + (p : 𝓞 D.F) ^ e * d - ε := by linear_combination hd
    rw [e0, map_sub, map_add, map_mul, hpe, hε0, map_one]
    ring
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hε
  obtain ⟨z, hz⟩ := mul_bar_eq r w hw hu
  have hb : D.bar ε = D.bar x * (p : 𝓞 D.F) + D.bar y * (D.bar D.ω - (r : 𝓞 D.F)) := by
    rw [← hxy]
    simp only [map_add, map_mul, map_sub, map_natCast, map_intCast]
  have hkey : π (D.ω - (r : 𝓞 D.F)) ∈ Ideal.span {π (p : 𝓞 D.F)} := by
    refine Ideal.mem_span_singleton'.2 ⟨π (D.bar x * (D.ω - (r : 𝓞 D.F)) + D.bar y * z), ?_⟩
    have e2 : (D.bar x * (D.ω - (r : 𝓞 D.F)) + D.bar y * z) * (p : 𝓞 D.F)
        = (D.ω - (r : 𝓞 D.F)) * D.bar ε := by
      rw [hb]
      linear_combination (-D.bar y) * hz
    rw [← map_mul, e2, map_mul, hbar1, _root_.mul_one]
  have hle : Ideal.map π (uIdeal D r) ≤ Ideal.span {π (p : 𝓞 D.F)} := by
    rw [uIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    rcases ha with rfl | rfl
    · exact Ideal.subset_span rfl
    · exact hkey
  intro u hu'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h2 : π u ∈ Ideal.span {π (p : 𝓞 D.F)} ^ e :=
    Ideal.pow_right_mono hle e (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hu')
  rw [Ideal.span_singleton_pow, ← map_pow, hpe] at h2
  simpa using h2

private theorem mem_of_pow_mem (I : Ideal (𝓞 D.F)) (e : ℕ) (ε : 𝓞 D.F) (hc : (p : 𝓞 D.F) ^ e ∈ I)
    (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1) (h2 : (p : 𝓞 D.F) ^ e ∣ ε * D.bar ε) (k : ℕ)
    (hk : ε ^ (k + 1) ∈ I) : ε ∈ I := by
  have hq : ε ^ 2 - ε ∈ I := by
    obtain ⟨d, hd⟩ := h1
    obtain ⟨f, hf⟩ := h2
    have e0 : ε ^ 2 - ε = (p : 𝓞 D.F) ^ e * (ε * d - f) := by linear_combination ε * hd - hf
    rw [e0]
    exact I.mul_mem_right _ hc
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    refine ih ?_
    have e1 : ε ^ (k + 1) = ε ^ (k + 1 + 1) - ε ^ k * (ε ^ 2 - ε) := by ring
    rw [e1]
    exact I.sub_mem hk (I.mul_mem_left _ hq)
end ring

section pts
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

private def ann (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) : Ideal (𝓞 D.F) where
  carrier := {x | g ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) = 1}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, o.act.add, MonObj.comp_mul, hx, hy, _root_.mul_one]
  zero_mem' := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    have h0 : o.act.act 0 = 1 := left_eq_mul.1 h
    simp only [Set.mem_setOf_eq]
    rw [map_zero, h0, MonObj.comp_one]
  smul_mem' := by
    intro y x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have := o.act.hom (algebraMap (𝓞 D.F) D.O y)
    rw [smul_eq_mul, map_mul, o.act.mul, ← Category.assoc, hx, MonObj.one_comp]

private theorem mem_ann {o : Obj b N s} {T : Over S} (g : T ⟶ o.A) (x : 𝓞 D.F) :
    x ∈ ann o g ↔ g ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) = 1 := Iff.rfl

private theorem killedBy_iff {o : Obj b N s} {T : Over S} (g : T ⟶ o.A) (v : Ideal (𝓞 D.F)) :
    KilledBy o v g ↔ v ≤ ann o g := Iff.rfl

private theorem act_natCast (o : Obj b N s) (n : ℕ) :
    o.act.act (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) = (𝟙 o.A) ^ n := by
  induction n with
  | zero =>
    have h := o.act.add 0 0
    rw [add_zero] at h
    have h0 : o.act.act 0 = 1 := left_eq_mul.1 h
    rw [Nat.cast_zero, map_zero, h0, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, map_add, o.act.add, ih, map_one, o.act.one, pow_succ]

private theorem natCast_mem_ann {o : Obj b N s} {T : Over S} (g : T ⟶ o.A) (n : ℕ) :
    (n : 𝓞 D.F) ∈ ann o g ↔ g ^ n = 1 := by
  rw [mem_ann, act_natCast, MonObj.comp_pow, Category.comp_id]

private theorem eq_one_of_rank_one {K A T : Over S} [GrpObj K] [GrpObj A] (i : K ⟶ A) [IsMonHom i]
    (h : IsIsogDeg (toUnit K) 1) (y : T ⟶ K) : y ≫ i = 1 := by
  have := h.fin
  have := h.flat
  have hiso : IsIso (toUnit K).left := by
    rw [Scheme.Hom.isIso_iff_finrank_eq]
    funext z
    exact h.rank z
  have : IsIso ((Over.forget S).map (toUnit K)) := hiso
  have : IsIso (toUnit K) := isIso_of_reflects_iso _ (Over.forget S)
  have hy : y = 1 := by
    rw [← cancel_mono (toUnit K)]
    exact toUnit_unique _ _
  rw [hy, MonObj.one_comp]

private theorem ann_push {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A) :
    ann Rd.o₀ a₀ = ann o (pushHom Rd.m₀.cart T₀ a₀) := by
  ext x
  exact GlobalTheory.IwLevel.comp_eq_one_iff_push Rd.m₀.cart Rd.m₀.cart (Rd.m₀.act _) a₀

private theorem tors_of_ker {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A) (h : a₀ ≫ Rd.ψ = 1) : a₀ ^ c = 1 := by
  obtain ⟨-, -, -, -, -, ψ', hψ', h1, -⟩ := Rd.isog
  have h2 : a₀ ≫ (𝟙 Rd.o₀.A) ^ c = 1 := by
    rw [← h1, ← Category.assoc, h, MonObj.one_comp]
  rwa [MonObj.comp_pow, Category.comp_id] at h2

private theorem tors_of_sub {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s}
    (hu : uIdeal D r ≤ w) (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (Sd : SubData w j o)
    {T : Over S} (x : T ⟶ o.A) (hx : InSub Sd.i x) : (c : 𝓞 D.F) ∈ ann o x := by
  obtain ⟨e, rfl, he⟩ := hc
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · have hj : j = 0 := by
      by_contra hj
      exact absurd (he (Nat.pos_of_ne_zero hj)) (lt_irrefl 0)
    subst hj
    have hdeg := Sd.deg
    rw [pow_zero] at hdeg
    obtain ⟨y, rfl⟩ := hx
    have := Sd.hom
    rw [natCast_mem_ann, eq_one_of_rank_one Sd.i hdeg y, one_pow]
  · have hp : (p : 𝓞 D.F) ∈ ann o x := Sd.killed T x hx _ (hu (p_mem_uIdeal D r))
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_of_mem _ hp e he0

private theorem core_fwd {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    (Sd : SubData w j o) (hu : uIdeal D r ≤ w) (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (e : ℕ)
    (hce : c = p ^ e) (ε : 𝓞 D.F) (hε : ε ∈ uIdeal D r) (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1)
    (h2 : (p : 𝓞 D.F) ^ e ∣ ε * D.bar ε) {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A)
    (H₁ : a₀ ^ c = 1 → a₀ ≫ Rd.ψ = 1 → a₀ ≫ Rd.o₀.act.act (algebraMap (𝓞 D.F) D.O ε) = 1 →
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀))
    (H₂ : a₀ ^ c = 1 → InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) → a₀ ≫ Rd.ψ = 1) :
    (a₀ ≫ Rd.ψ = 1 ∧ ∃ e : ℕ, KilledBy Rd.o₀ (uIdeal D r ^ e) a₀) ↔
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) := by
  constructor
  · rintro ⟨hψ, e', hk⟩
    have hcT := tors_of_ker Rd a₀ hψ
    have hcm : (p : 𝓞 D.F) ^ e ∈ ann Rd.o₀ a₀ := by
      have h3 := (natCast_mem_ann a₀ c).2 hcT
      have ec : (c : 𝓞 D.F) = (p : 𝓞 D.F) ^ e := by rw [hce, Nat.cast_pow]
      rwa [ec] at h3
    refine H₁ hcT hψ (mem_of_pow_mem (ann Rd.o₀ a₀) e ε hcm h1 h2 e' (hk _ ?_))
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hε e')
  · intro hs
    have hcm := tors_of_sub hu hc Sd _ hs
    rw [← ann_push] at hcm
    have hcT := (natCast_mem_ann a₀ c).1 hcm
    refine ⟨H₂ hcT hs, 1, ?_⟩
    rw [killedBy_iff, ann_push, pow_one]
    exact fun x hx => Sd.killed _ _ hs _ (hu hx)

private theorem core_bwd {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    (Sd : SubData w j o) (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) (e : ℕ)
    (hce : c = p ^ e) (ε : 𝓞 D.F) (hε : ε ∈ uIdeal D r) (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1)
    {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A)
    (H : (a₀ ≫ Rd.ψ = 1 ∧ ∃ e : ℕ, KilledBy Rd.o₀ (uIdeal D r ^ e) a₀) ↔
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀)) :
    (a₀ ^ c = 1 → a₀ ≫ Rd.ψ = 1 → a₀ ≫ Rd.o₀.act.act (algebraMap (𝓞 D.F) D.O ε) = 1 →
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀)) ∧
    (InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) → a₀ ≫ Rd.ψ = 1) := by
  refine ⟨fun hcT hψ hεa => H.1 ⟨hψ, e, ?_⟩, fun hs => (H.2 hs).1⟩
  have hcm : (p : 𝓞 D.F) ^ e ∈ ann Rd.o₀ a₀ := by
    have h3 := (natCast_mem_ann a₀ c).2 hcT
    have ec : (c : 𝓞 D.F) = (p : 𝓞 D.F) ^ e := by rw [hce, Nat.cast_pow]
    rwa [ec] at h3
  rw [killedBy_iff]
  refine (uIdeal_pow_le r w hw hu e ε hε h1).trans ?_
  rw [Ideal.span_le]
  rintro x (rfl | rfl)
  · exact hcm
  · exact hεa

private theorem two_locus (Y : Scheme.{0}) (A B₁ B₂ B' : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B₁] [GrpObj B₂]
    [GrpObj B'] (n : ℕ) (f₁ : A ⟶ B₁) (f₂ : A ⟶ B₂) (f' : A ⟶ B') (hA : IsAbelianScheme A)
    (h₁ : IsAbelianScheme B₁) (h₂ : IsAbelianScheme B₂) (h' : IsAbelianScheme B') [IsMonHom f₁] [IsMonHom f₂]
    [IsMonHom f'] (hn : IsUnit (n : Γ(Y, ⊤))) :
    ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧
      (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W → ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom →
        ∀ a : T ⟶ A, a ^ n = 1 → a ≫ f₁ = 1 → a ≫ f₂ = 1 → a ≫ f' = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔
        ∀ a : Over.mk x ⟶ A, a ^ n = 1 → a ≫ f₁ = 1 → a ≫ f₂ = 1 → a ≫ f' = 1 := by
  let Bf : Bool → Over Y := fun i => match i with
    | false => B₁
    | true => B₂
  letI gB : ∀ i, GrpObj (Bf i) := fun i => match i with
    | false => inferInstanceAs (GrpObj B₁)
    | true => inferInstanceAs (GrpObj B₂)
  let ff : ∀ i, A ⟶ Bf i := fun i => match i with
    | false => f₁
    | true => f₂
  obtain ⟨W, o, c, H, G⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y A n Bool Bf ff B' f' hA
    (fun i => match i with
      | false => h₁
      | true => h₂) h'
    (fun i => match i with
      | false => inferInstanceAs (IsMonHom f₁)
      | true => inferInstanceAs (IsMonHom f₂)) inferInstance hn
  have key : ∀ {T : Over Y} (a : T ⟶ A), (∀ i, a ≫ ff i = 1) ↔ (a ≫ f₁ = 1 ∧ a ≫ f₂ = 1) := fun a =>
    ⟨fun h => ⟨h false, h true⟩, fun h i => match i with
      | false => h.1
      | true => h.2⟩
  refine ⟨W, o, c, fun Tb t hW T σ hσ a ha g₁ g₂ => (H Tb t).1 hW T σ hσ a ha ((key a).2 ⟨g₁, g₂⟩),
    fun k _ _ x => (G k x).trans ?_⟩
  exact ⟨fun h a ha g₁ g₂ => h a ha ((key a).2 ⟨g₁, g₂⟩), fun h a ha g => h a ha ((key a).1 g).1 ((key a).1 g).2⟩

private theorem insub_push {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    (Sd : SubData w j o) (Tl : Scheme.{0}) (Th : Tl ⟶ S) (u : Tl ⟶ Rd.Y.left) (a₀ : Over.mk u ⟶ Rd.o₀.A)
    (a : Over.mk Th ⟶ o.A) (ha : a₀.left ≫ Rd.m₀.φ = a.left) :
    InSub Sd.i a ↔ InSub Sd.i (pushHom Rd.m₀.cart (Over.mk u) a₀) := by
  have hT : Th = u ≫ Rd.Y.hom := by
    have h₁ : a.left ≫ o.A.hom = Th := Over.w a
    have h₂ : a₀.left ≫ Rd.o₀.A.hom = u := Over.w a₀
    rw [← h₁, ← ha, Category.assoc, Rd.m₀.cart.1.w, ← Category.assoc, h₂]
  subst hT
  have ea : a = pushHom Rd.m₀.cart (Over.mk u) a₀ := Over.OverMorphism.ext ha.symm
  rw [ea]
end pts

section quot
open scoped CategoryTheory.Obj
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem exists_quot {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp R} {o : Obj b N s} (Rd : RepData b N r w j c s o) (Sd : SubData w j o) :
    ∃ (B₀ : Over Rd.Y.left) (_ : GrpObj B₀) (q₀ : Rd.o₀.A ⟶ B₀), IsAbelianScheme B₀ ∧ IsMonHom q₀ ∧
      ∀ {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A), a₀ ≫ q₀ = 1 ↔ InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) := by
  have hfin := Sd.fin
  have het := Sd.et
  have hflat : Flat Sd.K.hom := inferInstance
  have hSm := Sd.mono
  have hSh := Sd.hom
  obtain ⟨B, _, q, hab, hqm, -, -, -, hq⟩ :=
    GlobalTheory.IwLevel.quotGlobal_holds S o.A Sd.K Sd.i o.ab Sd.hom Sd.mono Sd.fin hflat
  have hker := GlobalTheory.UPel.HT.ES.IsogDVR.isPullback_kernel_of_kernelPair Sd.i q hq
  have hsub : ∀ {T : Over S} (x : T ⟶ o.A), x ≫ q = 1 ↔ InSub Sd.i x := by
    intro T x
    constructor
    · intro h
      exact ⟨hker.lift x (toUnit T) (by rw [h, Hom.one_def]), hker.lift_fst _ _ _⟩
    · rintro ⟨y, rfl⟩
      rw [Category.assoc, hker.w, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit T), Hom.one_def]
  have := hab.comm
  have hP := isGrpPullback_pullback B Rd.Y.hom
  obtain ⟨e₀, he₀m, he₀⟩ := grpPullback_iso Rd.m₀.cart (isGrpPullback_pullback o.A Rd.Y.hom)
  let q₀ : Rd.o₀.A ⟶ (Over.pullback Rd.Y.hom).obj B := e₀.hom ≫ (Over.pullback Rd.Y.hom).map q
  have hq₀m : IsMonHom q₀ := by
    have := he₀m
    infer_instance
  have hsq : q₀.left ≫ pullback.fst B.hom Rd.Y.hom = Rd.m₀.φ ≫ q.left := by
    have h3 : ((Over.pullback Rd.Y.hom).map q).left ≫ pullback.fst B.hom Rd.Y.hom =
        pullback.fst o.A.hom Rd.Y.hom ≫ q.left := pullback.lift_fst _ _ _
    rw [Over.comp_left, Category.assoc, h3, ← Category.assoc, he₀]
  exact ⟨_, inferInstance, q₀, GlobalTheory.isAbelianScheme_pullback_obj _ _ hab, hq₀m, fun a₀ =>
    (GlobalTheory.IwLevel.comp_eq_one_iff_push Rd.m₀.cart hP hsq a₀).trans (hsub _)⟩
end quot

theorem UpperTheory.exists_clopen_subgroup_locus :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), IsUnit ((p : ℕ) : R) → w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o), ∃ W : Set Rd.Y.left, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Rd.Y.left), Set.range t.base ⊆ W → KerAt Rd Sd t) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Rd.Y.left), Set.range y.base ⊆ W ↔ KerGeo Rd Sd y := by
  intro p _ D R _ b N r w j c hp hw hu hc S _ s o Rd Sd
  obtain ⟨e, hce, -⟩ := id hc
  have hwt : w ≠ ⊤ := hw.ne_top
  obtain ⟨ε, hε, h1, h2⟩ := UpperTheory.Cb.exists_mem_uIdeal_idempotent_mod_prime_pow p D r w e hwt hu
  obtain ⟨B₀, _, q₀, hB₀, hq₀m, hqp⟩ := exists_quot Rd Sd
  have hcu : IsUnit ((c : ℕ) : Γ(Rd.Y.left, ⊤)) := by
    have h3 := hp.map (gam (Rd.Y.hom ≫ s))
    rw [map_natCast] at h3
    have ec : ((c : ℕ) : Γ(Rd.Y.left, ⊤)) = ((p : ℕ) : Γ(Rd.Y.left, ⊤)) ^ e :=
      (congrArg Nat.cast hce).trans (Nat.cast_pow p e)
    rw [ec]
    exact h3.pow _
  have hψm : IsMonHom Rd.ψ := Rd.isog.2.1
  have hεm := Rd.o₀.act.hom (algebraMap (𝓞 D.F) D.O ε)
  obtain ⟨W₁, o₁, c₁, H₁, G₁⟩ := two_locus Rd.Y.left Rd.o₀.A Rd.o'.A Rd.o₀.A B₀ c Rd.ψ
    (Rd.o₀.act.act (algebraMap (𝓞 D.F) D.O ε)) q₀ Rd.o₀.ab Rd.o'.ab Rd.o₀.ab hB₀ hcu
  obtain ⟨W₂, o₂, c₂, H₂, G₂⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Rd.Y.left Rd.o₀.A c Unit (fun _ => B₀)
    (fun _ => q₀) Rd.o'.A Rd.ψ Rd.o₀.ab (fun _ => hB₀) Rd.o'.ab (fun _ => hq₀m) hψm hcu
  refine ⟨W₁ ∩ W₂, o₁.inter o₂, c₁.inter c₂, fun Tb t hW => ?_, fun k _ _ y => ?_⟩
  · have hW₁ := H₁ Tb t (hW.trans Set.inter_subset_left)
    have hW₂ := (H₂ Tb t).1 (hW.trans Set.inter_subset_right)
    intro T τ a₀ a ha
    exact (core_fwd Rd Sd hu hc e hce ε hε h1 h2 a₀
      (fun hcT hψ hεa => (hqp a₀).1 (hW₁ _ τ rfl a₀ hcT hψ hεa))
      (fun hcT hs => hW₂ _ τ rfl a₀ hcT (fun _ => (hqp a₀).2 hs))).trans
      (insub_push Rd Sd T.left T.hom (τ ≫ t) a₀ a ha).symm
  · rw [Set.subset_inter_iff, G₁, G₂]
    constructor
    · rintro ⟨g₁, g₂⟩ a₀ a ha
      have ea : a = pushHom Rd.m₀.cart (Over.mk y) a₀ := Over.OverMorphism.ext ha.symm
      subst ea
      exact core_fwd Rd Sd hu hc e hce ε hε h1 h2 a₀
        (fun hcT hψ hεa => (hqp a₀).1 (g₁ a₀ hcT hψ hεa))
        (fun hcT hs => g₂ a₀ hcT (fun _ => (hqp a₀).2 hs))
    · intro H
      refine ⟨fun a₀ hcT hψ hεa => ?_, fun a₀ hcT g => ?_⟩
      · exact (hqp a₀).2 ((core_bwd Rd Sd hwt hu e hce ε hε h1 a₀ (H a₀ _ rfl)).1 hcT hψ hεa)
      · exact (core_bwd Rd Sd hwt hu e hce ε hε h1 a₀ (H a₀ _ rfl)).2 ((hqp a₀).1 (g ()))
