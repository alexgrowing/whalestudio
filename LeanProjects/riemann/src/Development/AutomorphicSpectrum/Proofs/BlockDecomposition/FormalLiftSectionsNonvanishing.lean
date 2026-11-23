import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X : Scheme.{0}}

def nvl {M : LB X} {V : X.Opens} (s : SecOn M V) : X.Opens :=
  ⨆ i, X.basicOpen (GlobalTheory.LB.coord s i)

theorem basicOpen_unit_mul {W : X.Opens} (v : Γ(X, W)ˣ) (x : Γ(X, W)) :
    X.basicOpen ((v : Γ(X, W)) * x) = X.basicOpen x := by
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ v.isUnit]
  exact inf_eq_right.2 (X.basicOpen_le x)

theorem basicOpen_rs_eq_inf {U W : X.Opens} (h : W ≤ U) (x : Γ(X, U)) :
    X.basicOpen (rs X h x) = W ⊓ X.basicOpen x :=
  X.basicOpen_res x (homOfLE h).op

theorem mem_nvl_iff {M : LB X} {V : X.Opens} (s : SecOn M V) {p : X} (i : M.ι)
    (hp : p ∈ V ⊓ M.U i) : p ∈ nvl s ↔ p ∈ X.basicOpen (GlobalTheory.LB.coord s i) := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have hpj : p ∈ V ⊓ M.U j := X.basicOpen_le _ hj
    let W : X.Opens := (V ⊓ M.U i) ⊓ (V ⊓ M.U j)
    have hpW : p ∈ W := ⟨hp, hpj⟩
    have hij : W ≤ M.U i ⊓ M.U j := inf_le_inf inf_le_right inf_le_right
    have e := GlobalTheory.LB.coord_rel s i j (W := W) inf_le_left inf_le_right hij
    have e' : rs X (inf_le_left : W ≤ V ⊓ M.U i) (GlobalTheory.LB.coord s i) =
        ((Units.map (rs X hij).toMonoidHom (M.g i j) : Γ(X, W)ˣ) : Γ(X, W)) * rs X (inf_le_right : W ≤ V ⊓ M.U j) (GlobalTheory.LB.coord s j) := e
    have e2 := congrArg X.basicOpen e'
    rw [basicOpen_unit_mul, basicOpen_rs_eq_inf, basicOpen_rs_eq_inf] at e2
    have : p ∈ W ⊓ X.basicOpen (GlobalTheory.LB.coord s j) := ⟨hpW, hj⟩
    rw [← e2] at this
    exact this.2
  · intro h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, h⟩

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift
variable {X X' : Scheme.{0}}

theorem nvl_le {M : LB X} {V : X.Opens} (s : SecOn M V) : nvl s ≤ V :=
  iSup_le fun _ => (X.basicOpen_le _).trans inf_le_left

theorem exists_chart {M : LB X} (hM : M.IsLB) (p : X) : ∃ i, p ∈ M.U i := by
  have : p ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  exact TopologicalSpace.Opens.mem_iSup.1 this

theorem basicOpen_appLE (π : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (e : V ≤ π ⁻¹ᵁ U) (r : Γ(X, U)) :
    X'.basicOpen ((π.appLE U V e).hom r) = V ⊓ π ⁻¹ᵁ X.basicOpen r := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.preimage_basicOpen]
  exact X'.basicOpen_res _ _

theorem nvl_congr {L M : LB X} {V : X.Opens} (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M)
    (hw : w.IsGen) (s : SecOn L V) : nvl (SecOn.congr hL hM w hw V s) = nvl s := by
  ext p
  show p ∈ nvl (SecOn.congr hL hM w hw V s) ↔ p ∈ nvl s
  by_cases hp : p ∈ V
  · obtain ⟨a, ha⟩ := exists_chart hM p
    obtain ⟨b, hb⟩ := exists_chart hL p
    rw [mem_nvl_iff _ a ⟨hp, ha⟩, mem_nvl_iff _ b ⟨hp, hb⟩]
    let O : X.Opens := (V ⊓ M.U a) ⊓ (V ⊓ L.U b)
    have hO : p ∈ O := ⟨⟨hp, ha⟩, ⟨hp, hb⟩⟩
    have h : O ≤ M.U a ⊓ L.U b := inf_le_inf inf_le_right inf_le_right
    have e := SecOn.coord_congr hL hM w hw s a b (O := O) inf_le_left inf_le_right h
    have e' : rs X (inf_le_left : O ≤ V ⊓ M.U a) (GlobalTheory.LB.coord (SecOn.congr hL hM w hw V s) a) =
       ((Units.map (rs X h).toMonoidHom (show Γ(X, M.U a ⊓ L.U b)ˣ from w.s (a, b)) : Γ(X, O)ˣ) : Γ(X, O)) *
         rs X (inf_le_right : O ≤ V ⊓ L.U b) (GlobalTheory.LB.coord s b) := e
    have e2 := congrArg X.basicOpen e'
    rw [basicOpen_unit_mul, basicOpen_rs_eq_inf, basicOpen_rs_eq_inf] at e2
    constructor
    · intro hh
      have : p ∈ O ⊓ X.basicOpen (GlobalTheory.LB.coord (SecOn.congr hL hM w hw V s) a) := ⟨hO, hh⟩
      rw [e2] at this
      exact this.2
    · intro hh
      have : p ∈ O ⊓ X.basicOpen (GlobalTheory.LB.coord s b) := ⟨hO, hh⟩
      rw [← e2] at this
      exact this.2
  · exact ⟨fun h => absurd (nvl_le _ h) hp, fun h => absurd (nvl_le _ h) hp⟩

theorem nvl_pullLE {M : LB X} {V : X.Opens} (hM : M.IsLB) (π : X' ⟶ X) {V' : X'.Opens}
    (e : V' ≤ π ⁻¹ᵁ V) (s : SecOn M V) :
    nvl (SecOn.pullLE M π V V' e s) = V' ⊓ π ⁻¹ᵁ nvl s := by
  ext p
  show p ∈ nvl (SecOn.pullLE M π V V' e s) ↔ p ∈ V' ⊓ π ⁻¹ᵁ nvl s
  by_cases hp : p ∈ V'
  · obtain ⟨c, hc⟩ := exists_chart hM (π p)
    have hpV : π p ∈ V := e hp
    let j : (M.pull π).ι := fun _ => c
    have hj : p ∈ (M.pull π).U j := by
      show p ∈ (LB.wchart M _ j)
      exact Set.mem_iInter.2 fun _ => hc
    rw [mem_nvl_iff _ j ⟨hp, hj⟩, SecOn.coord_pullLE, basicOpen_appLE]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨hp, (mem_nvl_iff s c ⟨hpV, hc⟩).2 h⟩
    · rintro ⟨-, h⟩
      exact ⟨⟨hp, hj⟩, (mem_nvl_iff s c ⟨hpV, hc⟩).1 h⟩
  · exact ⟨fun h => absurd (nvl_le _ h) hp, fun h => absurd h.1 hp⟩

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift
section Tower
variable {R : Type} [CommRing R] (I : Ideal R)
  (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))

theorem nvl_redL (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : V' ≤ β e ⁻¹ᵁ V) (x : SecOn (L (e + 1)) V) :
    nvl ((SecOnR.of (toR I Y e) _ _).symm
      (redL I Y β hβ L w hL e V V' h (SecOnR.of (toR I Y (e + 1)) _ _ x))) =
      V' ⊓ β e ⁻¹ᵁ nvl x := by
  have hP := LB.isLB_pull (hL (e + 1)).1 (β e)
  rw [← nvl_pullLE (hL (e + 1)).1 (β e) h x, ← nvl_congr (hL e).1 hP (w e) (hL e).2]
  congr 1
  show SecOn.congr (hL e).1 hP (w e) (hL e).2 V' ((SecOn.congr (hL e).1 hP (w e) (hL e).2 V').symm _) = _
  exact (SecOn.congr (hL e).1 hP (w e) (hL e).2 V').apply_symm_apply _

include hβ in

theorem surjective_beta (e : ℕ) : Function.Surjective (β e) := by
  have hf : Function.Surjective (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1)) := Ideal.Quotient.factor_surjective _
  have h0 : AlgebraicGeometry.Surjective (thickTrans R I e) := by
    constructor
    intro p
    have hr := range_comap_of_surjective _ _ hf
    have hp : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ I ^ (e + 1 + 1) →+* R ⧸ I ^ (e + 1))) := by
      rw [hr]
      intro x hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hr' : r ∈ I ^ (e + 1) := by
        have := (RingHom.mem_ker).1 hx
        rw [Ideal.Quotient.factor_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.1 this
      have hsq : (Ideal.Quotient.mk (I ^ (e + 1 + 1)) r) ^ 2 = 0 := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two]
        refine Ideal.pow_le_pow_right (by omega : e + 1 + 1 ≤ (e + 1) + (e + 1)) ?_
        rw [pow_add]
        exact Ideal.mul_mem_mul hr' hr'
      exact p.isPrime.mem_of_pow_mem 2 (by rw [hsq]; exact Ideal.zero_mem _)
    exact hp
  exact (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) (hβ e).flip h0).surj
end Tower
end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift
section Tower2
variable {R : Type} [CommRing R] (I : Ideal R)
  (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
  (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
  (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen)
  {ι : Type} (D : ∀ e, Finset ι → (Y e).left.Opens)

include hβ in
theorem preimage_beta_injective (e : ℕ) {A B : (Y (e + 1)).left.Opens}
    (h : β e ⁻¹ᵁ A = β e ⁻¹ᵁ B) : A = B := by
  ext p
  obtain ⟨q, rfl⟩ := surjective_beta I Y β hβ e p
  have := congrArg (fun O : (Y e).left.Opens => q ∈ O) h
  exact iff_of_eq this

theorem nvl_tower (hD : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (a : ℤ) (S : Finset ι)
    (x : ∀ e, SecOn (pw (N e) a) (D e S))
    (hx : ∀ e, red I Y N D β hβ v hN (fun e S => (hD e S).ge) a e S (SecOnR.of _ _ _ (x (e + 1))) =
      SecOnR.of _ _ _ (x e))
    (O : ∀ e, (Y e).left.Opens) (hO : ∀ e, β e ⁻¹ᵁ O (e + 1) = O e) (h0 : nvl (x 0) = O 0) (e : ℕ) :
    nvl (x e) = O e := by
  induction e with
  | zero => exact h0
  | succ e ih =>
    apply preimage_beta_injective I Y β hβ e
    rw [hO e, ← ih]
    have h1 := nvl_redL I Y β hβ (fun e => pw (N e) a) (fun e => pullPow (v e) a)
      (fun e => ⟨isLB_pw (hN e).1 a, pullPow_isGen (v e) a (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hD e S).ge (x (e + 1))
    have h2 : β e ⁻¹ᵁ nvl (x (e + 1)) ≤ D e S := by
      rw [← hD e S]
      exact (β e).preimage_mono (nvl_le _)
    rw [inf_eq_right.2 h2] at h1
    rw [← h1]
    exact congrArg nvl (hx e).symm ▸ rfl

end Tower2

theorem nvl_ofSec {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) (V : X.Opens) :
    nvl (GlobalTheory.LB.ofSec s V : SecOn M V) = V ⊓ nonzeroLocus s := by
  rw [nonzeroLocus, inf_iSup_eq]
  refine iSup_congr fun i => ?_
  show X.basicOpen (rs X (inf_le_right : V ⊓ M.U i ≤ M.U i) (s.f i)) = _
  rw [basicOpen_rs_eq_inf, inf_assoc, inf_eq_right.2 (X.basicOpen_le (s.f i))]

theorem nvl_zero {X : Scheme.{0}} {M : LB X} (V : X.Opens) : nvl (0 : SecOn M V) = ⊥ := by
  refine le_antisymm (iSup_le fun i => ?_) bot_le
  rw [GlobalTheory.LB.coord_zero, Scheme.basicOpen_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem exists_pow_mul_eq_algebraMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (c g : B) (hn : IsNilpotent (c - algebraMap A B f)) :
    ∃ (k : ℕ) (h : A), algebraMap A B h = c ^ k * g := by
  obtain ⟨E, hE⟩ := hn
  set ν := c - algebraMap A B f with hν
  have hc : c = algebraMap A B f + ν := by rw [hν]; ring
  have key : ∀ x : B, ∃ n : ℕ, ∃ a : A, algebraMap A B a = algebraMap A B f ^ n * x := by
    intro x
    obtain ⟨n, a, hx⟩ := IsLocalization.Away.surj f x
    exact ⟨n, a, by rw [← hx]; ring⟩
  have key2 : ∀ x : B, ∃ n : ℕ, ∀ m, n ≤ m → ∃ a : A, algebraMap A B a = algebraMap A B f ^ m * x := by
    intro x
    obtain ⟨n, a, ha⟩ := key x
    refine ⟨n, fun m hm => ⟨f ^ (m - n) * a, ?_⟩⟩
    rw [map_mul, map_pow, ha, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm]
  choose n hn using fun i : ℕ => key2 (ν ^ i * g)
  let K : ℕ := (Finset.range E).sup n + E
  refine ⟨K, ?_⟩
  have hterm : ∀ i ∈ Finset.range (K + 1), ∃ a : A, algebraMap A B a =
      algebraMap A B f ^ (K - i) * ν ^ i * g * (K.choose i : B) := by
    intro i hi
    by_cases hiE : i < E
    · have h1 : n i ≤ K - i := by
        have : n i ≤ (Finset.range E).sup n := Finset.le_sup (Finset.mem_range.2 hiE)
        omega
      obtain ⟨a, ha⟩ := hn i _ h1
      refine ⟨a * (K.choose i : A), ?_⟩
      rw [map_mul, ha, map_natCast]
      ring
    · refine ⟨0, ?_⟩
      have : ν ^ i = 0 := pow_eq_zero_of_le (not_lt.1 hiE) hE
      rw [this]; simp
  choose! a ha using hterm
  refine ⟨∑ i ∈ Finset.range (K + 1), a i, ?_⟩
  rw [map_sum, Finset.sum_congr rfl ha, hc, add_comm (algebraMap A B f), add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  ring

end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift
section Core
variable {X : Scheme.{0}} {N : LB X}

abbrev ru {U W : X.Opens} (h : W ≤ U) : Γ(X, U)ˣ →* Γ(X, W)ˣ := Units.map (rs X h).toMonoidHom

theorem rs_refl {W : X.Opens} (h : W ≤ W) (x : Γ(X, W)) : rs X h x = x := by
  show (X.presheaf.map (homOfLE h).op).hom x = x
  have : (homOfLE h).op = 𝟙 (Opposite.op W) := rfl
  rw [this, X.presheaf.map_id]
  rfl

theorem le_iSup_inf_chart (hN : N.IsLB) (W : X.Opens) : W ≤ ⨆ i, W ⊓ N.U i := by
  rw [← inf_iSup_eq, hN.cover]
  exact le_inf le_rfl le_top

theorem fn_ext (hN : N.IsLB) {W : X.Opens} {g g' : Γ(X, W)}
    (h : ∀ i, rs X (inf_le_left : W ⊓ N.U i ≤ W) g = rs X inf_le_left g') : g = g' :=
  TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i => W ⊓ N.U i) W (fun i => homOfLE inf_le_left)
    (le_iSup_inf_chart hN W) g g' h

theorem exists_fn_zero (hN : N.IsLB) {a : ℤ} (ha : a = 0) {W : X.Opens} (x : SecOn (pw N a) W) :
    ∃ g : Γ(X, W), ∀ i : N.ι,
      (GlobalTheory.LB.coord (L := pw N a) x i : Γ(X, W ⊓ N.U i)) = rs X inf_le_left g := by
  subst ha
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i => W ⊓ N.U i) W
    (fun i => homOfLE inf_le_left) (le_iSup_inf_chart hN W)
    (fun i => (GlobalTheory.LB.coord (L := pw N 0) x i : Γ(X, W ⊓ N.U i))) (fun i j => by
      have hij : (W ⊓ N.U i) ⊓ (W ⊓ N.U j) ≤ N.U i ⊓ N.U j := inf_le_inf inf_le_right inf_le_right
      have e := GlobalTheory.LB.coord_rel (L := pw N 0) x i j (W := (W ⊓ N.U i) ⊓ (W ⊓ N.U j)) inf_le_left
        inf_le_right hij
      have e1 : (((pw N 0).g i j : Γ(X, (pw N 0).U i ⊓ (pw N 0).U j)ˣ) : Γ(X, (pw N 0).U i ⊓ (pw N 0).U j)) = 1 := by
        show ((N.g i j ^ (0 : ℤ) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) = 1
        rw [zpow_zero, Units.val_one]
      erw [e1, map_one, one_mul] at e
      exact e)
  exact ⟨g, fun i => (hg i).symm⟩

abbrev cd {c : ℤ} {W : X.Opens} (x : SecOn (pw N c) W) (i : N.ι) : Γ(X, W ⊓ N.U i) :=
  GlobalTheory.LB.coord (L := pw N c) x i

variable {d : ℤ} {V : X.Opens}

def genU (τ : SecOn (pw N d) V) (y : SecOn (pw N (-d)) V)
    (hy : secMulOn rfl τ y = oneOn N (add_neg_cancel d) V) (i : N.ι) : Γ(X, V ⊓ N.U i)ˣ where
  val := GlobalTheory.LB.coord (L := pw N d) τ i
  inv := GlobalTheory.LB.coord (L := pw N (-d)) y i
  val_inv := congrArg (fun z => GlobalTheory.LB.coord (L := pw N (d + -d)) z i) hy
  inv_val := (mul_comm (G := Γ(X, V ⊓ N.U i)) _ _).trans
    (congrArg (fun z => GlobalTheory.LB.coord (L := pw N (d + -d)) z i) hy)

theorem genU_rel (τ : SecOn (pw N d) V) (y : SecOn (pw N (-d)) V)
    (hy : secMulOn rfl τ y = oneOn N (add_neg_cancel d) V) (i j : N.ι) {O : X.Opens}
    (hi : O ≤ V ⊓ N.U i) (hj : O ≤ V ⊓ N.U j) (hij : O ≤ N.U i ⊓ N.U j) :
    ru hi (genU τ y hy i) = (ru hij (N.g i j)) ^ d * ru hj (genU τ y hy j) := by
  apply Units.ext
  have e := GlobalTheory.LB.coord_rel (L := pw N d) τ i j hi hj hij
  rw [Units.val_mul, ← map_zpow]
  exact e

def genPow (τ : SecOn (pw N d) V) (y : SecOn (pw N (-d)) V)
    (hy : secMulOn rfl τ y = oneOn N (add_neg_cancel d) V) (n c : ℤ) (hc : c = d * n) :
    SecOn (pw N c) V :=
  GlobalTheory.LB.mkSec (L := pw N c) (fun i => ((genU τ y hy i ^ n : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i)))
    (fun i j => by
      subst hc
      have hi : V ⊓ N.U i ⊓ N.U j ≤ V ⊓ N.U i := inf_le_left
      have hj : V ⊓ N.U i ⊓ N.U j ≤ V ⊓ N.U j := le_inf (inf_le_left.trans inf_le_left) inf_le_right
      have hij : V ⊓ N.U i ⊓ N.U j ≤ N.U i ⊓ N.U j :=
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have e := congrArg (· ^ n) (genU_rel τ y hy i j hi hj hij)
      simp only [mul_zpow, ← zpow_mul, ← map_zpow] at e
      exact congrArg Units.val e)

@[simp] theorem coord_genPow (τ : SecOn (pw N d) V) (y : SecOn (pw N (-d)) V)
    (hy : secMulOn rfl τ y = oneOn N (add_neg_cancel d) V) (n c : ℤ) (hc : c = d * n) (i : N.ι) :
    GlobalTheory.LB.coord (L := pw N c) (genPow τ y hy n c hc) i =
      ((genU τ y hy i ^ n : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i)) := rfl

end Core
end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift
section Core2
variable {X : Scheme.{0}} {N : LB X} {d : ℤ} {V : X.Opens}

theorem exists_fn (hN : N.IsLB) (τ : SecOn (pw N d) V) (y : SecOn (pw N (-d)) V)
    (hy : secMulOn rfl τ y = oneOn N (add_neg_cancel d) V) (n c : ℤ) (hc : c = d * n) {W : X.Opens}
    (h : W ≤ V) (x : SecOn (pw N c) W) :
    ∃ g : Γ(X, W), ∀ i : N.ι, cd x i =
      rs X inf_le_left g * rs X (inf_le_inf_right _ h)
        ((genU τ y hy i ^ n : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i)) := by
  let G : SecOn (pw N (-c)) W :=
    SecOn.restrict (pw N (-c)) h (genPow τ y hy (-n) (-c) (by rw [hc]; ring))
  obtain ⟨g, hg⟩ := exists_fn_zero hN (add_neg_cancel c) (secMulOn rfl x G)
  refine ⟨g, fun i => ?_⟩
  have e : cd x i * cd G i =
    rs X inf_le_left g := hg i
  have hG : cd G i =
      (((ru (inf_le_inf_right _ h) (genU τ y hy i ^ n))⁻¹ : Γ(X, W ⊓ N.U i)ˣ) : Γ(X, W ⊓ N.U i)) := by
    rw [← map_inv, ← zpow_neg]
    rfl
  rw [← e, hG]
  have : rs X (inf_le_inf_right _ h) ((genU τ y hy i ^ n : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i)) =
      ((ru (inf_le_inf_right _ h) (genU τ y hy i ^ n) : Γ(X, W ⊓ N.U i)ˣ) : Γ(X, W ⊓ N.U i)) := rfl
  rw [this, mul_assoc, Units.inv_mul, mul_one]

theorem nvl_eq_basicOpen (hN : N.IsLB) {c : ℤ} {W : X.Opens} (x : SecOn (pw N c) W) (g : Γ(X, W))
    (u : ∀ i : N.ι, Γ(X, W ⊓ N.U i)ˣ)
    (hx : ∀ i : N.ι, cd x i =
      rs X inf_le_left g * (u i : Γ(X, W ⊓ N.U i))) : nvl x = X.basicOpen g := by
  have e : ∀ i : N.ι, X.basicOpen (cd x i) =
      (W ⊓ N.U i) ⊓ X.basicOpen g := fun i => by
    rw [hx i, mul_comm, basicOpen_unit_mul, basicOpen_rs_eq_inf]
  show (⨆ i : N.ι, X.basicOpen (cd x i)) = _
  rw [iSup_congr e, ← iSup_inf_eq, ← inf_iSup_eq, hN.cover, inf_top_eq]
  exact inf_eq_right.2 (X.basicOpen_le g)

instance subsingleton_bot : Subsingleton Γ(X, (⊥ : X.Opens)) :=
  ⟨fun a b => TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun e : Empty => e.elim) ⊥
    (fun e : Empty => e.elim) bot_le a b (fun e : Empty => e.elim)⟩

theorem isNilpotent_of_basicOpen_eq_bot {W : X.Opens} (hW : IsAffineOpen W) (x : Γ(X, W))
    (h : X.basicOpen x = ⊥) : IsNilpotent x := by
  haveI := hW.isLocalization_basicOpen x
  have h1 : algebraMap Γ(X, W) Γ(X, X.basicOpen x) 1 = 0 := by
    have : Subsingleton Γ(X, X.basicOpen x) := by rw [h]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers x) Γ(X, X.basicOpen x) 1).1 h1
  exact ⟨k, by simpa using hk⟩

theorem core_kill (hN : N.IsLB) (hV : IsAffineOpen V) (τ σ : SecOn (pw N d) V)
    (y : SecOn (pw N (-d)) V) (hy : secMulOn rfl τ y = oneOn N (add_neg_cancel d) V)
    {V' : X.Opens} (h : V' ≤ V) (hσ : V' = nvl σ) (n c : ℤ) (hc : c = d * n) (a : SecOn (pw N c) V)
    (ha : SecOn.restrict (pw N c) h a = 0) :
    ∃ k : ℕ, ∀ i : N.ι, cd a i *
      cd σ i ^ k = 0 := by
  obtain ⟨f, hf⟩ := exists_fn hN τ y hy 1 d (by ring) le_rfl σ
  obtain ⟨g, hg⟩ := exists_fn hN τ y hy n c hc le_rfl a
  simp only [rs_refl] at hf hg
  have hbo : nvl σ = X.basicOpen f := nvl_eq_basicOpen hN σ f (fun i => genU τ y hy i ^ (1 : ℤ))
    (fun i => by rw [hf i])
  obtain rfl : V' = X.basicOpen f := hσ.trans hbo
  have g0 : rs X h g = 0 := by
    refine fn_ext hN (N := N) fun i => ?_
    have e : rs X (inf_le_inf_right (N.U i) h) (cd a i) = 0 :=
      congrArg (fun z => cd z i) ha
    rw [hg i, map_mul] at e
    have e2 := (((ru (inf_le_inf_right (N.U i) h) (genU τ y hy i ^ n)).isUnit).mul_left_eq_zero).1 e
    rw [map_zero, rs_rs]
    rw [rs_rs] at e2
    exact e2
  haveI := hV.isLocalization_basicOpen f
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Γ(X, X.basicOpen f) g).1 g0
  refine ⟨k, fun i => ?_⟩
  have hk' : rs X (inf_le_left : V ⊓ N.U i ≤ V) f ^ k * rs X inf_le_left g = 0 := by
    have := congrArg (rs X (inf_le_left : V ⊓ N.U i ≤ V)) hk
    simpa only [map_mul, map_pow, map_zero] using this
  rw [hg i, hf i, mul_pow]
  linear_combination ((genU τ y hy i ^ n : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i)) *
    ((genU τ y hy i ^ (1 : ℤ) : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i)) ^ k * hk'

end Core2
end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift
section Core3
variable {X : Scheme.{0}} {N : LB X} {d : ℤ} {V : X.Opens}

theorem core_extend (hN : N.IsLB) (hV : IsAffineOpen V) (τ σ : SecOn (pw N d) V)
    (y : SecOn (pw N (-d)) V) (hy : secMulOn rfl τ y = oneOn N (add_neg_cancel d) V)
    {V' : X.Opens} (h : V' ≤ V) (hσ : V' = nvl σ) (u : SecOn (pw N d) V')
    (hu : nvl (u - SecOn.restrict (pw N d) h σ) = ⊥) (t : ℤ) (b : SecOn (pw N (d * t)) V') :
    ∃ (k : ℕ) (a : SecOn (pw N (d * (t + k))) V), ∀ i : N.ι,
      cd (SecOn.restrict (pw N (d * (t + k))) h a) i = cd b i * cd u i ^ k := by
  obtain ⟨f, hf⟩ := exists_fn hN τ y hy 1 d (by ring) le_rfl σ
  simp only [rs_refl] at hf
  have hbo : nvl σ = X.basicOpen f := nvl_eq_basicOpen hN σ f (fun i => genU τ y hy i ^ (1 : ℤ))
    (fun i => by rw [hf i])
  obtain rfl : V' = X.basicOpen f := hσ.trans hbo
  obtain ⟨c, hc⟩ := exists_fn hN τ y hy 1 d (by ring) h u
  obtain ⟨g, hg⟩ := exists_fn hN τ y hy t (d * t) rfl h b
  have hν : X.basicOpen (c - rs X h f) = ⊥ := by
    rw [← hu]
    symm
    refine nvl_eq_basicOpen hN _ _
      (fun i => ru (inf_le_inf_right _ h) (genU τ y hy i ^ (1 : ℤ))) fun i => ?_
    have e1 : cd (u - SecOn.restrict (pw N d) h σ) i =
      cd u i - rs X (inf_le_inf_right _ h) (cd σ i) := rfl
    have e2 : ((ru (inf_le_inf_right _ h) (genU τ y hy i ^ (1 : ℤ)) : Γ(X, X.basicOpen f ⊓ N.U i)ˣ) :
        Γ(X, X.basicOpen f ⊓ N.U i)) = rs X (inf_le_inf_right _ h)
          ((genU τ y hy i ^ (1 : ℤ) : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i)) := rfl
    rw [e1, hc i, hf i, map_mul, e2, map_sub, rs_rs, rs_rs]
    ring
  have hnil := isNilpotent_of_basicOpen_eq_bot (hV.basicOpen f) _ hν
  haveI := hV.isLocalization_basicOpen f
  obtain ⟨k, h0, hh⟩ := exists_pow_mul_eq_algebraMap f c g hnil
  refine ⟨k, h0 • genPow τ y hy (t + k) (d * (t + k)) rfl, fun i => ?_⟩
  have e0 : rs X h h0 = c ^ k * g := hh
  have e1 : cd (SecOn.restrict (pw N (d * (t + k))) h
      (h0 • genPow τ y hy (t + k) (d * (t + k)) rfl)) i =
      rs X (inf_le_inf_right _ h) (rs X inf_le_left h0 *
        ((genU τ y hy i ^ (t + k) : Γ(X, V ⊓ N.U i)ˣ) : Γ(X, V ⊓ N.U i))) := rfl
  have e2 : rs X (inf_le_inf_right (N.U i) h) (rs X (inf_le_left : V ⊓ N.U i ≤ V) h0) =
      rs X inf_le_left c ^ k * rs X inf_le_left g := by
    have := congrArg (rs X (inf_le_left : X.basicOpen f ⊓ N.U i ≤ X.basicOpen f)) e0
    rw [map_mul, map_pow, rs_rs] at this
    rw [rs_rs]
    exact this
  have e3 : genU τ y hy i ^ (t + k) = genU τ y hy i ^ t * (genU τ y hy i ^ (1 : ℤ)) ^ k := by
    rw [zpow_add, zpow_one, zpow_natCast]
  rw [e1, map_mul, e2, hg i, hc i, e3, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
    mul_pow]
  ring

end Core3

section Gr
variable {R : Type} [CommRing R] (I : Ideal R)
  (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (N : ∀ e, LB (Y e).left) {ι : Type} (D : ∀ e, Finset ι → (Y e).left.Opens) (d : ℤ)

theorem exists_X_pow_smul (e : ℕ) (S : Finset ι) (σ : ι → SecOn (pw (N e) d) (D e S))
    (hc : OperatorsCommute (ι := ι) (R := R) (A := fun t => Tm I Y N D d e t S)
      fun j t => mulT I Y N D d e t S (σ j)) (j : ι) (t : ℤ) (a : Tm I Y N D d e t S) (k : ℕ) :
    ∀ (t' : ℤ), t' = t + k → ∃ c : Tm I Y N D d e t' S,
      (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of hc t a = GrSum.of hc t' c ∧
      ∀ i : (N e).ι, cd (N := N e) ((SecOnR.of _ _ _).symm c) i =
        cd (N := N e) ((SecOnR.of _ _ _).symm a) i * cd (N := N e) (σ j) i ^ k := by
  induction k with
  | zero =>
    intro t' ht
    obtain rfl : t' = t := by simpa using ht
    exact ⟨a, by simp, fun i => by simp⟩
  | succ k ih =>
    intro t' ht
    obtain ⟨c, hc1, hc2⟩ := ih (t + k) rfl
    obtain rfl : t' = t + k + 1 := by rw [ht]; push_cast; ring
    refine ⟨mulT I Y N D d e (t + k) S (σ j) c, ?_, fun i => ?_⟩
    · rw [pow_succ' (MvPolynomial.X j : MvPolynomial ι R) k, mul_smul, hc1, GrSum.X_smul_of]
    · have e1 : cd (N := N e) ((SecOnR.of _ _ _).symm (mulT I Y N D d e (t + k) S (σ j) c)) i =
        cd (N := N e) ((SecOnR.of _ _ _).symm c) i * cd (N := N e) (σ j) i := rfl
      rw [e1, hc2 i, pow_succ (cd (N := N e) (σ j) i) k, mul_assoc]

end Gr
end GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem localisation_grSum : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)), (∀ e S j t (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e t (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e S) t a = 0) ∧ (∀ e S j t (b : Tm I Y N D (d : ℤ) e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : Tm I Y N D (d : ℤ) e t' S), GrSum.of (hc e (insert j S)) t' (resT I Y N D (d : ℤ) hDm e t' (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e (insert j S)) t b) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  have key1 : ∀ e S j, S.Nonempty → D e (insert j S) = nvl (sh e j S) := fun e S j hS =>
    (nvl_tower I Y β hβ N v hN D hDβ (d : ℤ) S (fun e => sh e j S) (fun e => hshp e j S hS)
      (fun e => D e (insert j S)) (fun e => hDβ e _) (by
        rw [hsh0 j S hS, nvl_ofSec, hD0, hD0, Finset.iInf_insert, inf_comm]) e).symm
  have key2 : ∀ e S j, S.Nonempty → nvl (sh e j (insert j S) - SecOn.restrict (pw (N e) (d : ℤ))
      (hDm e S (insert j S) (Finset.subset_insert j S)) (sh e j S)) = ⊥ := fun e S j hS => by
    refine nvl_tower I Y β hβ N v hN D hDβ (d : ℤ) (insert j S)
      (fun e => sh e j (insert j S) - SecOn.restrict (pw (N e) (d : ℤ))
        (hDm e S (insert j S) (Finset.subset_insert j S)) (sh e j S)) (fun e => ?_)
      (fun _ => ⊥) (fun e => rfl) ?_ e
    · have h1 := hshp e j (insert j S) (Finset.insert_nonempty j S)
      have h2 := hshp e j S hS
      have h3 := redL_restrict R I Y β hβ (fun e => pw (N e) (d : ℤ)) (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
        (D (e + 1) (insert j S)) (D e S) (D e (insert j S)) (hDβ e S).ge (hDβ e _).ge
        (hDm (e + 1) S (insert j S) (Finset.subset_insert j S))
        (hDm e S (insert j S) (Finset.subset_insert j S)) (SecOnR.of _ _ _ (sh (e + 1) j S))
      have h3' : red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e (insert j S)
          (SecOnR.restrict _ _ (hDm (e + 1) S (insert j S) (Finset.subset_insert j S))
            (SecOnR.of _ _ _ (sh (e + 1) j S))) =
          SecOnR.restrict _ _ (hDm e S (insert j S) (Finset.subset_insert j S))
            (red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S
              (SecOnR.of _ _ _ (sh (e + 1) j S))) := h3
      rw [h2] at h3'
      exact (map_sub _ _ _).trans (congrArg₂ (· - ·) h1 h3')
    · rw [hsh0 j _ (Finset.insert_nonempty j S), hsh0 j S hS, SecOn.restrict_ofSec, sub_self,
        nvl_zero]
  refine ⟨?_, ?_⟩
  · intro e S j t a hS ha
    obtain ⟨i0, hi0⟩ := id hS
    obtain ⟨y, hy⟩ := hshu e i0 S hi0
    obtain ⟨k, hk⟩ := core_kill (hN e).1 (hDa e S hS) (sh e i0 S) (sh e j S) y hy
      (hDm e S _ (Finset.subset_insert j S)) (key1 e S j hS) t _ rfl a ha
    obtain ⟨c, hc1, hc2⟩ := exists_X_pow_smul I Y N D (d : ℤ) e S (fun j => sh e j S) (hc e S) j t a k
      (t + k) rfl
    refine ⟨k, ?_⟩
    have hc0 : c = 0 := GlobalTheory.LB.sec_ext fun i => (hc2 i).trans (hk i)
    rw [hc1, hc0, map_zero]
  · intro e S j t b hS
    obtain ⟨i0, hi0⟩ := id hS
    obtain ⟨y, hy⟩ := hshu e i0 S hi0
    obtain ⟨k, a, ha⟩ := core_extend (hN e).1 (hDa e S hS) (sh e i0 S) (sh e j S) y hy
      (hDm e S _ (Finset.subset_insert j S)) (key1 e S j hS) (sh e j (insert j S)) (key2 e S j hS) t b
    obtain ⟨c, hc1, hc2⟩ := exists_X_pow_smul I Y N D (d : ℤ) e (insert j S)
      (fun j' => sh e j' (insert j S)) (hc e (insert j S)) j t b k (t + k) rfl
    refine ⟨k, t + k, a, ?_⟩
    rw [hc1]
    congr 1
    exact GlobalTheory.LB.sec_ext fun i => (ha i).trans (hc2 i).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
