import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechAugRow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotalComplexFlipIsomorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatTransUpToSqPullbackStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace CrystallineSemistableComparison.Auxfb
variable {R : Type} [CommRing R]

theorem zsm_cancel {M : Type*} [AddCommGroup M] (n : ℕ) (a : M) (h : (-1 : ℤ) ^ n • a = 0) : a = 0 := by
  have := congrArg (fun b => (-1 : ℤ) ^ n • b) h
  simpa [smul_smul, ← mul_pow] using this

theorem Dmem' (K : DCx.{w} R) (N : ℕ) (y : ∀ p q, K.X p q) (hy : ∀ p q, p + q + 1 ≠ N → y p q = 0) :
    K.D y ∈ K.T N := by
  intro p q h
  rcases p with _ | p <;> rcases q with _ | q
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, hy 0 q (by omega)]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, hy p 0 (by omega)]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, hy p (q + 1) (by omega), hy (p + 1) q (by omega)]

end CrystallineSemistableComparison.Auxfb

namespace CrystallineSemistableComparison.Auxfb
variable {R : Type} [CommRing R]

theorem stair (K : DCx.{w} R) (s : R) (N : ℕ)
    (hex : ∀ p q, p + q + 1 = N → ExactUpTo s (K.dv p q) (K.dv p (q + 1)))
    (x : ∀ p q, K.X p q) (hx : x ∈ K.T N) (hD : ∀ p q, K.D x p (q + 1) = 0) :
    ∀ k, k ≤ N → ∃ y : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ N → y p q = 0) ∧
      ∀ p q, N - k < q → (s ^ k • x - K.D y) p q = 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨0, fun _ _ _ => rfl, fun p q hq => ?_⟩
    simp only [pow_zero, one_smul, map_zero, sub_zero]
    exact hx p q (by omega)
  | succ k ih =>
    intro hk
    obtain ⟨y, hy, hs⟩ := ih (by omega)
    set x' := s ^ k • x - K.D y with hx'
    have hx'T : x' ∈ K.T N := Submodule.sub_mem _ (Submodule.smul_mem _ _ hx) (Dmem' K N y hy)
    have hDx' : ∀ p q, K.D x' p (q + 1) = 0 := by
      intro p q
      rw [hx', map_sub, K.DD, sub_zero, map_smul]
      simp [hD p q]
    obtain ⟨r, hr⟩ : ∃ r, N = k + r + 1 := ⟨N - k - 1, by omega⟩
    have hv : K.dv k (r + 1) (x' k (r + 1)) = 0 := by
      have h1 := hDx' k (r + 1)
      rw [DCx.D_apply] at h1
      have h2 : K.Dh x' k (r + 1 + 1) = 0 := by
        rcases k with _ | a
        · rfl
        · show K.dh a (r + 1 + 1) (x' a (r + 1 + 1)) = 0
          rw [hs a (r + 1 + 1) (by omega), map_zero]
      rw [h2, zero_add] at h1
      exact zsm_cancel k _ h1
    obtain ⟨w, hw⟩ := hex k r (by omega) _ hv
    refine ⟨s • y + (-1 : ℤ) ^ k • K.sgl k r w, fun p q hpq => ?_, fun p q hq => ?_⟩
    · show s • y p q + (-1 : ℤ) ^ k • K.sgl k r w p q = 0
      rw [hy p q hpq, K.sgl_ne w (by omega)]
      simp
    · have hsq : ((-1 : ℤ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
      have e : s ^ (k + 1) • x - K.D (s • y + (-1 : ℤ) ^ k • K.sgl k r w) =
          s • x' - (-1 : ℤ) ^ k • K.sgl (k + 1) r (K.dh k r w) - K.sgl k (r + 1) (s • x' k (r + 1)) := by
        rw [map_add, map_smul, map_zsmul, K.D_sgl, hw, hx', smul_add, smul_smul ((-1 : ℤ) ^ k), hsq, one_smul,
          pow_succ', mul_smul, smul_sub]
        abel
      rw [e]
      simp only [Pi.sub_apply, Pi.smul_apply]
      rw [K.sgl_ne (K.dh k r w) (Or.inr (by omega) : p ≠ k + 1 ∨ q ≠ r), smul_zero, sub_zero]
      by_cases hq1 : q = r + 1
      · subst hq1
        by_cases hp : p = k
        · subst hp; rw [K.sgl_self, sub_self]
        · rw [hx'T p (r + 1) (by omega), K.sgl_ne _ (Or.inl hp)]; simp
      · rw [show x' p q = 0 from hs p q (by omega), K.sgl_ne _ (Or.inr hq1)]; simp

theorem stair_top (K : DCx.{w} R) (s : R) (N : ℕ)
    (hex : ∀ p q, p + q + 1 = N → ExactUpTo s (K.dv p q) (K.dv p (q + 1)))
    (x : ∀ p q, K.X p q) (hx : x ∈ K.T N) (hD : ∀ p q, K.D x p (q + 1) = 0) :
    ∃ y : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ N → y p q = 0) ∧
      s ^ N • x - K.D y = K.sgl N 0 ((s ^ N • x - K.D y) N 0) := by
  obtain ⟨y, hy, hs⟩ := stair K s N hex x hx hD N le_rfl
  refine ⟨y, hy, ?_⟩
  have hT : s ^ N • x - K.D y ∈ K.T N := Submodule.sub_mem _ (Submodule.smul_mem _ _ hx) (Dmem' K N y hy)
  funext p q
  by_cases h : p = N ∧ q = 0
  · obtain ⟨rfl, rfl⟩ := h; rw [K.sgl_self]
  · rw [K.sgl_ne _ (by omega)]
    rcases q with _ | q
    · exact hT p 0 (by omega)
    · exact hs p (q + 1) (by omega)

end CrystallineSemistableComparison.Auxfb

namespace CrystallineSemistableComparison.Auxfb
theorem hom_ext {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ ψ : Cx.Hom K L σ) (h : φ.f = ψ.f) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl
end CrystallineSemistableComparison.Auxfb

theorem CrystallineSemistableComparison.P.dc_col_surj : ∀ {R : Type} [CommRing R] {A : Cx.{w'} R} {K : DCx.{w} R} (e : DCx.AugCol A K) (s : R) (n : ℕ), (∀ p q, p + q + 1 = n → ExactUpTo s (K.dv p q) (K.dv p (q + 1))) → ExactUpTo s (e.η n) (K.dv n 0) → InjUpTo s (e.η (n + 1)) → SurjUpTo (s ^ (n + 2)) (e.edge.mapH n) := by
  intro R _ A K e s n hcol hη hinj c
  obtain ⟨x, hx, rfl⟩ := (P.cls_surj K.tot n).1 c
  have hD : K.D x.1 = 0 := congrArg Subtype.val hx
  obtain ⟨y, hy, hxy⟩ := Auxfb.stair_top K s n hcol x.1 x.2 (fun p q => by rw [hD]; rfl)
  set z := (s ^ n • x.1 - K.D y) n 0 with hz
  have hDz : K.D (K.sgl n 0 z) = 0 := by rw [← hxy, map_sub, K.DD, sub_zero, map_smul, hD, smul_zero]
  rw [K.D_sgl] at hDz
  have hv : K.dv n 0 z = 0 := by
    have h := congrFun (congrFun hDz n) 1
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      K.sgl_ne (K.dh n 0 z) (Or.inl (by omega) : n ≠ n + 1 ∨ 1 ≠ 0), K.sgl_self, zero_add] at h
    exact Auxfb.zsm_cancel n _ h
  have hh : K.dh n 0 z = 0 := by
    have h := congrFun (congrFun hDz (n + 1)) 0
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, K.sgl_self,
      K.sgl_ne (K.dv n 0 z) (Or.inl (by omega) : n + 1 ≠ n ∨ 0 ≠ 0 + 1), smul_zero, add_zero] at h
    exact h
  obtain ⟨a, ha⟩ := hη z hv
  have hda : s • A.d n a = 0 := hinj _ (by rw [← e.comm, ha, map_smul, hh, smul_zero])
  have hb : A.d n (s • a) = 0 := by rw [map_smul, hda]
  have hb' : K.tot.d n (e.edge.f n (s • a)) = 0 := by rw [e.edge.comm, hb, map_zero]
  refine ⟨A.cls (s • a) hb, ?_⟩
  rw [P.mapH_cls _ n _ hb hb', ← (P.cls_surj K.tot n).2.2.2.2 (s ^ (n + 2)) x hx (by rw [map_smul, hx, smul_zero]),
    (P.cls_surj K.tot n).2.2.1]
  have key : (e.edge.f n (s • a)).1 - s ^ (n + 2) • x.1 = K.D (-(s ^ 2 • y)) := by
    rw [show (e.edge.f n (s • a)).1 = K.sgl n 0 (e.η n (s • a)) from rfl, map_smul, ha, smul_smul, map_smul,
      ← hxy, map_neg, map_smul]
    module
  cases n with
  | zero =>
    have hy0 : y = 0 := funext fun p => funext fun q => hy p q (by omega)
    show _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    exact Subtype.ext (key.trans (by rw [hy0]; simp))
  | succ m =>
    have hyT : -(s ^ 2 • y) ∈ K.T m :=
      Submodule.neg_mem _ (Submodule.smul_mem _ _ fun p q h => hy p q (by omega))
    exact ⟨⟨_, hyT⟩, Subtype.ext key.symm⟩

theorem CrystallineSemistableComparison.P.dc_col_inj : ∀ {R : Type} [CommRing R] {A : Cx.{w'} R} {K : DCx.{w} R} (e : DCx.AugCol A K) (s : R) (n : ℕ), (∀ p q, p + q + 2 = n → ExactUpTo s (K.dv p q) (K.dv p (q + 1))) → (∀ m, m + 1 = n → ExactUpTo s (e.η m) (K.dv m 0)) → InjUpTo s (e.η n) → InjUpTo (s ^ (n + 2)) (e.edge.mapH n) := by
  intro R _ A K e s n hcol hη hinj c hc
  obtain ⟨a, ha, rfl⟩ := (P.cls_surj A n).1 c
  have hb' : K.tot.d n (e.edge.f n a) = 0 := by rw [e.edge.comm, ha, map_zero]
  rw [P.mapH_cls _ n a ha hb', (P.cls_surj K.tot n).2.1] at hc
  rw [← (P.cls_surj A n).2.2.2.2 _ a ha (by rw [map_smul, ha, smul_zero]), (P.cls_surj A n).2.1]
  cases n with
  | zero =>
    have h0 : e.edge.f 0 a = 0 := (Submodule.mem_bot R).1 hc
    have h00 : K.sgl 0 0 (e.η 0 a) 0 0 = 0 := congrFun (congrFun (congrArg Subtype.val h0) 0) 0
    rw [K.sgl_self] at h00
    have hs := hinj a h00
    show _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, pow_succ, mul_smul, hs, smul_zero]
  | succ m =>
    obtain ⟨Y, hY⟩ := hc
    have hDY : K.D Y.1 = K.sgl (m + 1) 0 (e.η (m + 1) a) := congrArg Subtype.val hY
    obtain ⟨y, hy, hyy⟩ := Auxfb.stair_top K s m (fun p q h => hcol p q (by omega)) Y.1 Y.2
      (fun p q => by rw [hDY]; exact K.sgl_ne _ (Or.inr (by omega)))
    set w := (s ^ m • Y.1 - K.D y) m 0 with hw
    have hDw : K.D (K.sgl m 0 w) = s ^ m • K.sgl (m + 1) 0 (e.η (m + 1) a) := by
      rw [← hyy, map_sub, K.DD, sub_zero, map_smul, hDY]
    rw [K.D_sgl] at hDw
    have hv : K.dv m 0 w = 0 := by
      have h := congrFun (congrFun hDw m) 1
      simp only [Pi.add_apply, Pi.smul_apply] at h
      rw [K.sgl_ne (K.dh m 0 w) (Or.inl (by omega) : m ≠ m + 1 ∨ 1 ≠ 0), K.sgl_self, zero_add,
        K.sgl_ne (e.η (m + 1) a) (Or.inl (by omega) : m ≠ m + 1 ∨ 1 ≠ 0), smul_zero] at h
      exact Auxfb.zsm_cancel m _ h
    have hh : K.dh m 0 w = s ^ m • e.η (m + 1) a := by
      have h := congrFun (congrFun hDw (m + 1)) 0
      simp only [Pi.add_apply, Pi.smul_apply] at h
      rw [K.sgl_self, K.sgl_self, K.sgl_ne (K.dv m 0 w) (Or.inl (by omega) : m + 1 ≠ m ∨ 0 ≠ 0 + 1),
        smul_zero, add_zero] at h
      exact h
    obtain ⟨b, hb⟩ := hη m rfl w hv
    have h1 : e.η (m + 1) (A.d m b - s ^ (m + 1) • a) = 0 := by
      rw [map_sub, ← e.comm, hb, map_smul, hh, map_smul, smul_smul, ← pow_succ', sub_self]
    have h2 := hinj _ h1
    rw [smul_sub, sub_eq_zero] at h2
    refine ⟨s ^ 2 • b, ?_⟩
    rw [map_smul, pow_two, mul_smul, h2, smul_smul, smul_smul]
    congr 1; ring

theorem CrystallineSemistableComparison.P.dc_flip : ∀ {R : Type} [CommRing R] (K : DCx.{w} R), ∃ φ : Cx.Hom K.tot K.flip.tot (RingHom.id R), (∀ n, Function.Bijective (φ.f n)) ∧ ∀ n (x : K.tot.X n) p q, (φ.f n x).1 q p = (-1 : ℤ) ^ (p * q) • x.1 p q := GlobalTheory.T.total_complex_flip_isomorphism

theorem CrystallineSemistableComparison.P.dc_col : ∀ {R : Type} [CommRing R] {A : Cx.{w'} R} {K : DCx.{w} R} (e : DCx.AugCol A K) (s : R), (∀ p, (K.col p).ResUpTo s (e.η p)) → ∀ n, UpTo (s ^ (n + 2)) (e.edge.mapH n) := by
  intro R _ A K e s hres n
  exact ⟨P.dc_col_inj e s n (fun p q _ => (hres p).2.2.2 q) (fun m _ => (hres m).2.2.1) (hres n).2.1,
    P.dc_col_surj e s n (fun p q _ => (hres p).2.2.2 q) (hres n).2.2.1 (hres (n + 1)).2.1⟩

theorem CrystallineSemistableComparison.P.dc_row : ∀ {R : Type} [CommRing R] {A : Cx.{w'} R} {K : DCx.{w} R} (e : DCx.AugRow A K) (s : R), (∀ q, (K.row q).ResUpTo s (e.ε q)) → ∀ n, UpTo (s ^ (n + 2)) (e.edge.mapH n) := by
  intro R _ A K e s hres n
  let e' : DCx.AugCol A K.flip := ⟨e.ε, e.hε, e.comm⟩
  have hc := P.dc_col e' s (fun p => hres p) n
  obtain ⟨φ, hbij, hφ⟩ := P.dc_flip K
  have heq : (e.edge.comp φ : Cx.Hom A K.flip.tot (RingHom.id R)) = e'.edge := by
    apply Auxfb.hom_ext
    funext m
    refine LinearMap.ext fun a => Subtype.ext (funext fun q => funext fun p => ?_)
    show (φ.f m (e.edge.f m a)).1 q p = K.flip.sgl m 0 (e.ε m a) q p
    rw [hφ]
    show (-1 : ℤ) ^ (p * q) • K.sgl 0 m (e.ε m a) p q = K.flip.sgl m 0 (e.ε m a) q p
    by_cases hp : p = 0
    · subst hp
      by_cases hq : q = m
      · subst hq; rw [K.sgl_self, K.flip.sgl_self]; simp
      · rw [K.sgl_ne _ (Or.inr hq), K.flip.sgl_ne _ (Or.inl hq)]; simp
    · rw [K.sgl_ne _ (Or.inl hp), K.flip.sgl_ne _ (Or.inr hp)]; simp
  have hg : UpTo (1 : R) (φ.mapH n) := ((P.upTo_alg (φ.mapH n) LinearMap.id 1 1).2.2.2.2).2 (P.mapH_bij φ hbij n)
  have hcomp : (φ.mapH n) ∘ₗ (e.edge.mapH n) = e'.edge.mapH n := by
    refine LinearMap.ext fun x => ?_
    rw [← heq, P.mapH_comp]; rfl
  have := (P.upTo_alg (e.edge.mapH n) (φ.mapH n) 1 (s ^ (n + 2))).2.2.1 hg (hcomp ▸ hc)
  rwa [one_mul] at this

theorem CrystallineSemistableComparison.P.coef_upTo : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {F F' : C ⥤ ModuleCat.{w} R} (α : F ⟶ F') (s : R), (∀ T, UpTo s (α.app T).hom) → ∀ n, UpTo (s ^ 2) ((Mor.ofNatTrans α).pull n) := GlobalTheory.T.natTrans_upTo_sq_pullback
