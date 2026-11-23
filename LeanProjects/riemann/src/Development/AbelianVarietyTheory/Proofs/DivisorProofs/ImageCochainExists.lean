import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

namespace CupSpec

variable {R : Type} [CommRing R]

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g :=
  ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x

section Cup
variable {I J K : Cx R} (μ : Pair I J K) {E : Spc}

def awF {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U) : Sec (K.X w) U :=
  ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev a p _ rfl U (x.sub 0 p (by omega))) (ev b (N - p) _ rfl U (x.sub p (N - p) (by omega)))

theorem awF_res {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) :
    Sec.res g (awF μ hk a b N w h U x) = awF μ hk a b N w h V (x.res g) := by
  unfold awF
  rw [Sec.res, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, sub_res, sub_res, ← ev_res, ← ev_res, ← μ.nat]

theorem isAW_exists {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) (b : Cochain ((chains R).obj E) J m) :
    ∃ c, μ.IsAW hk a b c := by
  obtain ⟨c, hc⟩ := ev_exists (awF μ hk a b) (fun N w h V U g x => awF_res μ hk a b N w h g x)
  exact ⟨c, hc⟩

theorem isAW_unique {n m k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b c') : c = c' :=
  ev_ext c c' fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm

theorem isAW_add_left {n m k : ℤ} (hk : n + m = k) {a a' : Cochain ((chains R).obj E) I n} {b : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a' b c') : μ.IsAW hk (a + a') b (c + c') := by
  intro N w hw U x
  rw [ev_add, h N w hw U x, h' N w hw U x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_add, map_add, LinearMap.add_apply, smul_add]

theorem isAW_add_right {n m k : ℤ} (hk : n + m = k) {a : Cochain ((chains R).obj E) I n} {b b' : Cochain ((chains R).obj E) J m}
    {c c' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk a b c) (h' : μ.IsAW hk a b' c') : μ.IsAW hk a (b + b') (c + c') := by
  intro N w hw U x
  rw [ev_add, h N w hw U x, h' N w hw U x, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev_add, map_add, smul_add]

theorem isAW_zero_left {n m k : ℤ} (hk : n + m = k) (b : Cochain ((chains R).obj E) J m) : μ.IsAW hk 0 b 0 := by
  intro N w hw U x
  simp [ev_zero]

theorem isAW_zero_right {n m k : ℤ} (hk : n + m = k) (a : Cochain ((chains R).obj E) I n) : μ.IsAW hk a 0 0 := by
  intro N w hw U x
  simp [ev_zero]

theorem aw_cocycle {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (c : Cochain ((chains R).obj E) K k) (hc : μ.IsAW hk α.1 β.1 c) : δ k (k + 1) c = 0 := by
  have h₁ : μ.IsAW (by omega : (n + 1) + m = k + 1) (δ n (n + 1) α.1) β.1 0 := by
    rw [Cocycle.δ_eq_zero]; exact isAW_zero_left μ _ _
  have h₂ : μ.IsAW (by omega : n + (m + 1) = k + 1) α.1 (δ m (m + 1) β.1) 0 := by
    rw [Cocycle.δ_eq_zero]; exact isAW_zero_right μ _ _
  rw [aw_leibniz μ rfl rfl rfl hc h₁ h₂]
  simp

def awc {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Cocycle.mk (isAW_exists μ hk α.1 β.1).choose (k + 1) rfl (aw_cocycle μ hk α β _ (isAW_exists μ hk α.1 β.1).choose_spec)

theorem awc_spec {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (awc μ hk α β).1 := (isAW_exists μ hk α.1 β.1).choose_spec

theorem awc_eq {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : awc μ hk α β = γ :=
  Cocycle.ext (isAW_unique μ hk (awc_spec μ hk α β) h)

def cupL {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) :
    CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun β => CohomologyClass.mk (awc μ hk α β)) (fun β β' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact awc_eq μ hk _ _ _ (isAW_add_right μ hk (awc_spec μ hk α β) (awc_spec μ hk α β'))))
    (by
      rintro ⟨b, hb⟩ ⟨m', hm', b', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨c₀, hc₀⟩ := isAW_exists μ (rfl : n + m' = n + m') α.1 b'
      have h₁ : μ.IsAW (by omega : (n + 1) + m' = k) (δ n (n + 1) α.1) b' 0 := by
        rw [Cocycle.δ_eq_zero]; exact isAW_zero_left μ _ _
      have hL := aw_leibniz μ rfl hm' (by omega) hc₀ h₁ (awc_spec μ hk α ⟨_, hb⟩)
      refine ⟨n + m', by omega, n.negOnePow • c₀, ?_⟩
      rw [δ_units_smul, hL, zero_add, smul_smul, Int.units_mul_self, one_smul])

theorem cupL_mk {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    cupL μ hk α (CohomologyClass.mk β) = CohomologyClass.mk (awc μ hk α β) := rfl

def cupMap {n m k : ℤ} (hk : n + m = k) :
    CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => cupL μ hk α) (fun α α' => by
      ext y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      rw [AddMonoidHom.add_apply, cupL_mk, cupL_mk, cupL_mk, ← CohomologyClass.mk_add]; congr 1
      exact awc_eq μ hk _ _ _ (isAW_add_left μ hk (awc_spec μ hk α β) (awc_spec μ hk α' β))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      ext y
      obtain ⟨β, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨c₀, hc₀⟩ := isAW_exists μ (rfl : n' + m = n' + m) a' β.1
      have h₂ : μ.IsAW (by omega : n' + (m + 1) = k) a' (δ m (m + 1) β.1) 0 := by
        rw [Cocycle.δ_eq_zero]; exact isAW_zero_right μ _ _
      have hL := aw_leibniz μ hn' rfl (by omega) hc₀ (awc_spec μ hk ⟨_, ha⟩ β) h₂
      refine ⟨n' + m, by omega, c₀, ?_⟩
      rw [hL, smul_zero, add_zero])

end Cup

section Op
variable {S : Type} [CommRing S] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) {E : Spc} {n : ℤ}

theorem image_cochain_exists (a : Cochain ((chains S).obj E) I n) : ∃ b, ρ.IsImage a b :=
  ev_exists (fun p s h U x => ρ.app U s (ev a p s h U x)) (fun p s h V U g x => by rw [ρ.nat, ev_res])

theorem image_unique {a : Cochain ((chains S).obj E) I n} {b b' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) (h' : ρ.IsImage a b') : b = b' :=
  ev_ext b b' fun p s hs U x => (h p s hs U x).trans (h' p s hs U x).symm

theorem image_add {a a' : Cochain ((chains S).obj E) I n} {b b' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) (h' : ρ.IsImage a' b') : ρ.IsImage (a + a') (b + b') := fun p s hs U x => by
  rw [ev_add, ev_add, map_add, h p s hs, h' p s hs]

theorem image_zero : ρ.IsImage (0 : Cochain ((chains S).obj E) I n) 0 := fun p s hs U x => by
  rw [ev_zero, ev_zero, map_zero]

theorem image_δ {m : ℤ} (hm : n + 1 = m) {a : Cochain ((chains S).obj E) I n} {b : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) : ρ.IsImage (δ n m a) (δ n m b) := by
  intro p t ht U x
  cases p with
  | zero => rw [ev_δ_zero hm b U _ t rfl, ev_δ_zero hm a U _ t rfl, h, ρ.comm]
  | succ p =>
    rw [ev_δ_succ hm b U p _ t rfl, ev_δ_succ hm a U p _ t rfl, h, ρ.comm, map_add, sg_smul, sg_smul, map_zsmul, map_sum]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, h]

theorem image_pull {E' : Spc} (f : E' ⟶ E) {a : Cochain ((chains S).obj E) I n} {b : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage a b) : ρ.IsImage ((Cochain.ofHom ((chains S).map f)).comp a (zero_add n))
      ((Cochain.ofHom ((chains R).map f)).comp b (zero_add n)) := fun p s hs U x => by
  rw [ev_pull, ev_pull, h]

def imgc (α : Cocycle ((chains S).obj E) I n) : Cocycle ((chains R).obj E) J n :=
  Cocycle.mk (image_cochain_exists ρ α.1).choose (n + 1) rfl (by
    have h := image_δ ρ rfl (image_cochain_exists ρ α.1).choose_spec
    rw [Cocycle.δ_eq_zero] at h
    exact image_unique ρ h (image_zero ρ))

theorem imgc_spec (α : Cocycle ((chains S).obj E) I n) : ρ.IsImage α.1 (imgc ρ α).1 :=
  (image_cochain_exists ρ α.1).choose_spec

theorem imgc_eq (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n) (h : ρ.IsImage α.1 β.1) :
    imgc ρ α = β := Cocycle.ext (image_unique ρ (imgc_spec ρ α) h)

def opMap : NatOp I J where
  app E n := CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => CohomologyClass.mk (imgc ρ α)) (fun α α' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact imgc_eq ρ _ _ (image_add ρ (imgc_spec ρ α) (imgc_spec ρ α'))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨b, hb⟩ := image_cochain_exists ρ a'
      exact ⟨n', hn', b, image_unique ρ (image_δ ρ hn' hb) (imgc_spec ρ ⟨_, ha⟩)⟩)
  nat f n x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (imgc_eq ρ (zcomp (Cocycle.ofHom ((chains S).map f)) x (zero_add n))
      (zcomp (Cocycle.ofHom ((chains R).map f)) (imgc ρ x) (zero_add n)) (image_pull ρ f (imgc_spec ρ x))).symm

end Op

end CupSpec

open CupSpec

theorem Pair.cup_spec {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k) :
    μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ := by
  intro h
  have hP : ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
      CohomologyClass ((chains R).obj E) K k, ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k),
        μ.IsAW hk α.1 β.1 γ.1 → c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    ⟨cupMap μ hk, fun α β γ h => by
      change CohomologyClass.mk (awc μ hk α β) = _
      rw [awc_eq μ hk α β γ h]⟩
  exact pick_spec hP α β γ h

theorem Pair.aw_exists {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) : ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 :=
  ⟨awc μ hk α β, awc_spec μ hk α β⟩

theorem SemiMap.op_spec {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
    (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n) :
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) →
    ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  pick_spec (P := fun c : NatOp I J => ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n)
    (β : Cocycle ((chains R).obj E) J n),
    (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U),
      ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) → c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β)
    ⟨opMap ρ, fun _ _ α β h => congrArg CohomologyClass.mk (imgc_eq ρ α β h)⟩ E n α β

theorem SemiMap.image_exists {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
    (α : Cocycle ((chains S).obj E) I n) : ∃ β : Cocycle ((chains R).obj E) J n,
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x) :=
  ⟨imgc ρ α, imgc_spec ρ α⟩

theorem cup_op_spec :
    (∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
      (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
      (∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ γ : Cocycle ((chains R).obj E) K k,
        μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ) ∧
    ∀ {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (E : Spc) (n : ℤ)
      (α : Cocycle ((chains S).obj E) I n),
      (∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧ ∀ β : Cocycle ((chains R).obj E) J n,
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  ⟨fun μ E _ _ _ hk α β => ⟨μ.aw_exists E hk α β, μ.cup_spec E hk α β⟩,
    fun ρ E n α => ⟨ρ.image_exists E n α, ρ.op_spec E n α⟩⟩

end GlobalTheory.EtC

end
