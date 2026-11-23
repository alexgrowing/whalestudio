import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeTateCokerSharp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

theorem mem_of_forall_dvd {O A : Type} [CommRing O] [IsDomain O] [ValuationRing O] [AddCommGroup A]
    [Module O A] [Module.IsTorsionFree O A] (N : Submodule O A) (hN : N.FG) {q : O} (hq : q ≠ 0)
    (hqN : ∀ a, q • a ∈ N) (x : A)
    (h : ∀ φ : A →ₗ[O] O, (∀ y ∈ N, q ∣ φ y) → q ∣ φ x) : x ∈ N := by
  classical
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  haveI : Module.Flat O N := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  haveI : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O N
  let ψ : A →ₗ[O] N := LinearMap.codRestrict N (q • LinearMap.id) (fun a => hqN a)
  have hψ : ∀ a, (ψ a : A) = q • a := fun a => rfl
  have key : ∀ i, q ∣ b.coord i (ψ x) := by
    intro i
    apply h ((b.coord i).comp ψ)
    intro y hy
    have hy' : ψ y = q • (⟨y, hy⟩ : N) := Subtype.ext (hψ y)
    rw [LinearMap.comp_apply, hy', map_smul, smul_eq_mul]
    exact dvd_mul_right _ _
  choose d hd using key
  let z : N := ∑ i, d i • b i
  have hz : ψ x = q • z := by
    apply b.ext_elem
    intro i
    have := hd i
    simp only [Module.Basis.coord_apply] at this
    simp [z, this, Finset.smul_sum, smul_smul, Finsupp.single_apply]
  have hxz : x = (z : A) := by
    have h1 : q • x = q • (z : A) := by
      rw [← hψ, hz]; rfl
    exact Module.IsTorsionFree.isSMulRegular (isRegular_of_ne_zero hq) h1
  rw [hxz]
  exact z.2

variable {p : ℕ} {O : Type} [CommRing O]

theorem dUnit_mulBy {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ) (a : A) :
    dUnit O (mulBy O A k a) = (k : O) • dUnit O a := by
  rw [← cotMap_d]
  show cotMap ((toConv (BialgHom.id O A) ^ k).ofConv) (dUnit O a) = _
  rw [cotMap_pow, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  simp [cotMap_id]

theorem dUnit_of_mem_torsionIdeal {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ)
    {t : A} (ht : t ∈ torsionIdeal O A k) : ∃ y, dUnit O t = (k : O) • y := by
  suffices H : counitAlgHom O A t = 0 ∧ ∃ y, dUnit O t = (k : O) • y from H.2
  change t ∈ Ideal.span _ at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, dUnit O a, dUnit_mulBy k a⟩
    have ha' : counitAlgHom O A a = 0 := ha
    simpa using ha'
  | zero => exact ⟨by simp, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx0, u, hu⟩ := hx
    obtain ⟨hy0, v, hv⟩ := hy
    exact ⟨by rw [map_add, hx0, hy0, add_zero], u + v, by simp [hu, hv, smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨hx0, u, hu⟩ := hx
    refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], counitAlgHom O A c • u, ?_⟩
    show AugCot.d _ (c * x) = _
    rw [AugCot.d_mul, hx0, zero_smul, add_zero]
    change _ • dUnit O x = _
    rw [hu, smul_comm]

theorem exists_of_cotMap_res_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A (n + 1)))
    (hy : cotMap (G.res n) y = 0) : ∃ y', y = (p : O) ^ n • y' := by
  unfold cotMap at hy
  obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map _ _ (G.res_surjective n) y).1 hy
  have hx' : dUnit O (x : G.A (n + 1)) = y := by
    rw [← hx]
    exact (AugCot.kerMap_apply _ _ x).symm
  have hxmem : (x : G.A (n + 1)) ∈ torsionIdeal O (G.A (n + 1)) (p ^ n) := by
    rw [← G.ker_res n]
    exact x.2
  obtain ⟨y', hy'⟩ := dUnit_of_mem_torsionIdeal (p ^ n) hxmem
  refine ⟨y', ?_⟩
  rw [← hx', ← Nat.cast_pow]
  exact hy'

def lev (G : PDivGroup p O) (n : ℕ) : G.omega →ₗ[O] Cot O (G.A n) :=
  LinearMap.proj n ∘ₗ G.omegaSub.subtype

theorem lev_apply (G : PDivGroup p O) (n : ℕ) (w : G.omega) : lev G n w = w.1 n := rfl

private theorem prime_pow_smul_cot_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A n)) :
    (p : O) ^ n • y = 0 := by
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ y
  obtain ⟨a, rfl⟩ := G.res_surjective n b
  set r := counitAlgHom O (G.A (n + 1)) a
  have hmem : mulBy O (G.A (n + 1)) (p ^ n) (a - algebraMap O _ r) ∈ RingHom.ker (G.res n) := by
    rw [G.ker_res n]
    apply Ideal.mem_map_of_mem
    show a - algebraMap O _ r ∈ RingHom.ker (counitAlgHom O (G.A (n + 1)))
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp [r]
  have h2 : G.res n (mulBy O _ (p ^ n) a) = algebraMap O _ r := by
    rw [RingHom.mem_ker] at hmem
    have := hmem
    simp only [map_sub, AlgHomClass.commutes, sub_eq_zero] at this
    exact this
  rw [← Nat.cast_pow]
  change ((p ^ n : ℕ) : O) • dUnit O (G.res n a) = 0
  rw [← dUnit_mulBy, ← map_mulBy, h2]
  exact AugCot.d_algebraMap _ _

theorem smul_mem_of_levels [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O)
    (L : Submodule O G.omega) (hL : L.FG) (κ : O)
    (hκ : ∀ n (y : Cot O (G.A n)), κ • y ∈ L.map (lev G n))
    (hp : ∀ n (y : Cot O (G.A n)), (p : O) • y ∈ L.map (lev G n)) (w : G.omega) : κ • w ∈ L := by
  classical
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let g : (Fin m → O) →ₗ[O] G.omega := Fintype.linearCombination O s
  have hg : LinearMap.range g = L := by rw [Fintype.range_linearCombination, hs]
  let Φ : (k : ℕ) → (Fin m → O) →ₗ[O] Cot O (G.A k) := fun k => (lev G k).comp g
  have compat : ∀ k (v : G.omega), cotMap (G.res k) (lev G (k + 1) v) = lev G k v := by
    intro k v
    rw [lev_apply, lev_apply]
    exact v.2 k
  have compatΦ : ∀ k c, cotMap (G.res k) (Φ (k + 1) c) = Φ k c := fun k c => compat k (g c)
  have lift : ∀ k (y : Cot O (G.A k)), y ∈ L.map (lev G k) → ∃ c, Φ k c = y := by
    intro k y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    rw [← hg] at hv
    obtain ⟨c, rfl⟩ := hv
    exact ⟨c, rfl⟩
  let W : (k : ℕ) → Cot O (G.A k) := fun k => lev G k w
  have hWc : ∀ k, cotMap (G.res k) (κ • W (k + 1)) = κ • W k := by
    intro k
    rw [map_smul, compat]
  have step : ∀ n (c : {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}),
      ∃ c' : {c : Fin m → O // Φ (n + 2) c = κ • W (n + 2)},
        ∃ f : Fin m → O, c'.1 = c.1 + (p : O) ^ n • f := by
    intro n c
    obtain ⟨d, hd⟩ := lift (n + 2) _ (hκ (n + 2) (W (n + 2)))
    have hd1 : Φ (n + 1) d = κ • W (n + 1) := by
      rw [← compatΦ, hd, hWc]
    have he : cotMap (G.res (n + 1)) (Φ (n + 2) (d - c.1)) = 0 := by
      rw [compatΦ, map_sub, hd1, c.2, sub_self]
    obtain ⟨y', hy'⟩ := exists_of_cotMap_res_eq_zero G (n + 1) _ he
    obtain ⟨f, hf⟩ := lift (n + 2) _ (hp (n + 2) y')
    refine ⟨⟨c.1 + (p : O) ^ n • f, ?_⟩, f, rfl⟩
    have key : Φ (n + 2) (d - c.1) = Φ (n + 2) ((p : O) ^ n • f) := by
      rw [hy', map_smul, hf, smul_smul, ← pow_succ]
    have : c.1 + (p : O) ^ n • f = d - (d - c.1) + (p : O) ^ n • f := by abel
    rw [this, map_add, map_sub, key, hd]
    abel
  choose nxt hnxt using step
  obtain ⟨c0, hc0⟩ := lift 1 _ (hκ 1 (W 1))
  let seq : (n : ℕ) → {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)} :=
    fun n => @Nat.rec (fun n => {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}) ⟨c0, hc0⟩
      (fun k ck => nxt k ck) n
  have seq_succ : ∀ n, seq (n + 1) = nxt n (seq n) := fun n => rfl
  have diff : ∀ a b, a ≤ b → ∃ t : Fin m → O, (seq b).1 = (seq a).1 + (p : O) ^ a • t := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ b hab ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨f, hf⟩ := hnxt b (seq b)
      refine ⟨t + (p : O) ^ (b - a) • f, ?_⟩
      rw [seq_succ, hf, ht, smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hab, add_assoc]
  have hpre : ∀ j, ∃ l : O, ∀ n, (seq n).1 j ≡ l [SMOD ((Ideal.span {(p : O)}) ^ n • ⊤ : Submodule O O)] := by
    intro j
    apply IsPrecomplete.prec inferInstance
    intro a b hab
    obtain ⟨t, ht⟩ := diff a b hab
    rw [SModEq.sub_mem, ht]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_add_cancel_left, Ideal.mul_top]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) a))
  choose l hl using hpre
  have close : ∀ N, ∃ t : Fin m → O, l = (seq N).1 + (p : O) ^ N • t := by
    intro N
    have : ∀ j, ∃ a : O, a * (p : O) ^ N = l j - (seq N).1 j := by
      intro j
      have h1 := (SModEq.sub_mem.1 (hl j N).symm)
      simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h1
      exact Ideal.mem_span_singleton'.1 h1
    choose t ht using this
    refine ⟨t, funext fun j => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ht]
    ring
  have good : ∀ n, Φ (n + 1) l = κ • W (n + 1) := by
    intro n
    obtain ⟨t, ht⟩ := close (n + 1)
    have h1 : Φ (n + 1) (seq (n + 1)).1 = κ • W (n + 1) := by
      rw [← compatΦ, (seq (n + 1)).2, hWc]
    rw [ht, map_add, h1, map_smul, prime_pow_smul_cot_eq_zero, add_zero]
  have good' : ∀ n, Φ n l = κ • W n := by
    intro n
    cases n with
    | zero => rw [← compatΦ, good 0, hWc]
    | succ n => exact good n
  have hgl : g l = κ • w := by
    apply Subtype.ext
    funext k
    have := good' k
    simp only [Φ, W, LinearMap.comp_apply, lev_apply] at this
    rw [this]
    rfl
  rw [← hg, ← hgl]
  exact LinearMap.mem_range_self g l

end PositivityTheory.HtPt.Farsharp
