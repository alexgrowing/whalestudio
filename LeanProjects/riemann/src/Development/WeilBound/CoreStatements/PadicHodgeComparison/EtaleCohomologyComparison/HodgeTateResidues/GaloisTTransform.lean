import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dividedPowerFiltration_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) : pdP δ 1 = J := by
  refine le_antisymm (Ideal.span_le.2 ?_) fun z hz => by simpa using pow_mem_pdP δ hz 1
  rintro _ ⟨L, hL, hr, rfl⟩
  induction L with
  | nil => simp at hr
  | cons q L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons] at hr ⊢
    rcases Nat.eq_zero_or_pos q.1 with h | h
    · exact J.mul_mem_left _ (ih (fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')) (by omega))
    · exact J.mul_mem_right _ (δ.dpow_mem h.ne' (hL q List.mem_cons_self))

structure Br (R : Per l K) (Y : CB l K) (e : Y.Λ →+* R.A) (θP : R.P →+* ℂ_[l]) (sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ)
    (sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n) (sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]) (c : K.fixingSubgroup → ℂ_[l]) : Prop where
  et : e Y.t = R.t
  t_ne : R.tB ≠ 0
  θ_i : ∀ x, ∃ y : R.P, (y : R.B) = R.i (e x) ∧ θP y = Y.θ x
  θ_o : ∀ k : K, ∃ y : R.P, (y : R.B) = R.o k ∧ θP y = kC K k
  ker : ∀ x : R.P, θP x = 0 ↔ ∃ y : R.P, (x : R.B) = R.tB * y
  θ_σ : ∀ (g : K.fixingSubgroup) (x : R.P), ∃ y : R.P, R.σ g x = y ∧ θP y = sC g (θP x)
  galois_t_transform : ∀ g : K.fixingSubgroup, ∃ u : R.P, R.σ g R.tB = u * R.tB ∧ θP u = c g
  eσ : ∀ g x, e (sΛ g x) = R.σA g (e x)
  cris : ∀ g n x, sn g n (Y.c n x) = Y.c n (sΛ g x)

variable {R : Per l K} {Y : CB l K} {e : Y.Λ →+* R.A} {θP : R.P →+* ℂ_[l]} {sΛ : K.fixingSubgroup → Y.Λ →+* Y.Λ}
  {sn : K.fixingSubgroup → ∀ n, Y.R n →+* Y.R n} {sC : K.fixingSubgroup → ℂ_[l] →+* ℂ_[l]} {c : K.fixingSubgroup → ℂ_[l]}
  (hb : Br R Y e θP sΛ sn sC c) {m : ℕ} {L : Lev R m} (hL : L.Good)

include hb hL

theorem Br.θ_ex : ∃ θ : L.B →+* ℂ_[l], ∀ x, θ (L.toB x) = θP x := by
  refine ⟨(L.toB.liftOfSurjective hL.toB_surj) ⟨θP, fun x hx => ?_⟩, fun x => RingHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  obtain ⟨y, hy⟩ := (hL.toB_ker x).1 hx
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  rw [hb.et] at ht
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hL.pos
  refine (hb.ker x).2 ⟨t ^ k * y, ?_⟩
  rw [hy, hk, pow_add, pow_one, Subring.coe_mul, SubmonoidClass.coe_pow, ht, mul_assoc]
  rfl

theorem Br.t_ex : ∃ t : R.P, (t : R.B) = R.tB ∧ L.ι (L.lam (e Y.t)) = L.toB t ∧ L.IB = Ideal.span {L.toB t} := by
  obtain ⟨t, ht, -⟩ := hb.θ_i Y.t
  refine ⟨t, by rw [ht, hb.et]; rfl, hL.ι_lam _ t ht, ?_⟩
  rw [← dividedPowerFiltration_one L.γB, hL.pdP_B 1 t (by rw [ht, hb.et]; rfl), pow_one]

def Br.θ : L.B →+* ℂ_[l] := (hb.θ_ex hL).choose

theorem Br.θ_toB (x : R.P) : hb.θ hL (L.toB x) = θP x := (hb.θ_ex hL).choose_spec x

theorem Br.ker_θ : RingHom.ker (hb.θ hL) = L.IB := by
  obtain ⟨t, ht, -, hI⟩ := hb.t_ex hL
  ext b
  obtain ⟨x, rfl⟩ := hL.toB_surj b
  rw [RingHom.mem_ker, hb.θ_toB, hI, Ideal.mem_span_singleton']
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (hb.ker x).1 h
    refine ⟨L.toB y, ?_⟩
    rw [← map_mul]
    exact congrArg L.toB (Subtype.ext (by rw [hy, Subring.coe_mul, ht, mul_comm]))
  · rintro ⟨a, ha⟩
    have h0 : θP t = 0 := (hb.ker t).2 ⟨1, by rw [ht]; simp⟩
    rw [← hb.θ_toB hL, ← ha, map_mul, hb.θ_toB, h0, mul_zero]

theorem Br.gr (i : ℕ) (hi : i < m) (x : L.B)
    (h : x * L.ι (L.lam (e Y.t)) ^ i ∈ Ideal.span {L.ι (L.lam (e Y.t)) ^ (i + 1)}) : x ∈ L.IB := by
  obtain ⟨t, ht, h1, hI⟩ := hb.t_ex hL
  rw [h1] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨x, rfl⟩ := hL.toB_surj x
  obtain ⟨a, rfl⟩ := hL.toB_surj a
  have h2 : L.toB (x * t ^ i - a * t ^ (i + 1)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, ha, sub_self]
  obtain ⟨y, hy⟩ := (hL.toB_ker _).1 h2
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have h3 : x = (a + t ^ k * y) * t := by
    refine Subtype.ext (mul_right_cancel₀ (pow_ne_zero i hb.t_ne) ?_)
    push_cast at hy ⊢
    rw [ht] at hy ⊢
    linear_combination hy
  rw [hI, h3, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def Br.lv (hd : ∀ n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) L.γ l n, ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ (L.lam (e x))) :
    Lv Y m where
  B := L.B
  IB := L.IB
  γB := L.γB
  θ := hb.θ hL
  A := L.A
  I := L.I
  γ := L.γ
  ι := L.ι
  lam := L.lam.comp e
  d n := (hd n).choose
  d_lam n := (hd n).choose_spec
  lat := hL.lat m le_rfl
  ι_dp := hL.ι_dp
  ι_O := hL.ι_O
  t_mem := by
    obtain ⟨t, -, h1, hI⟩ := hb.t_ex hL
    rw [hL.ι_I, Ideal.mem_comap, RingHom.comp_apply, h1, hI]
    exact Ideal.mem_span_singleton_self _
  θ_K k := by
    obtain ⟨y, h1, h2⟩ := hb.θ_o k
    rw [← hL.toB_K k y h1, hb.θ_toB, h2]
  θ_lam x := by
    obtain ⟨y, h1, h2⟩ := hb.θ_i x
    rw [RingHom.comp_apply, hL.ι_lam _ y h1, hb.θ_toB, h2]
  ker_θ := hb.ker_θ hL
  pdB r := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, hL.pdP_B r t ht]
  nil := by
    obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
    rw [RingHom.comp_apply, h1, ← map_pow]
    exact (hL.toB_ker _).2 ⟨1, by simp [ht]⟩
  gr := hb.gr hL

theorem Br.gal (hd) (g : K.fixingSubgroup) : Nonempty (LHom (hb.lv hL hd) (hb.lv hL hd) (sΛ g) (sn g) (sC g) (c g)) := by
  obtain ⟨u, hu, hc⟩ := hb.galois_t_transform g
  obtain ⟨t, ht, h1, -⟩ := hb.t_ex hL
  exact ⟨{
    le := le_rfl
    sA := L.σA g
    sB := L.σB g
    dpA := hL.σ_dp g
    dpB := hL.σB_dp g
    oA := hL.σ_O g
    oB := hL.σB_K g
    ι := fun a => (hL.σ_ι g a).symm
    lam := fun x => (hL.σ_lam g (e x)).trans (congrArg L.lam (hb.eσ g x).symm)
    cris := hb.cris g
    θ := fun b => by
      obtain ⟨x, rfl⟩ := hL.toB_surj b
      obtain ⟨y, h2, h3⟩ := hb.θ_σ g x
      change hb.θ hL (L.σB g (L.toB x)) = sC g (hb.θ hL (L.toB x))
      rw [hL.σB_toB g x y h2, hb.θ_toB, hb.θ_toB, h3]
    cB := L.toB u
    t := by
      change L.σB g (L.ι (L.lam (e Y.t))) = L.toB u * L.ι (L.lam (e Y.t))
      rw [h1, ← map_mul]
      exact hL.σB_toB g t (u * t) (by rw [Subring.coe_mul, ht, hu])
    θc := (hb.θ_toB hL u).trans hc }⟩

omit hL in
theorem Br.sys (S : LevSys R) (hS : S.Good)
    (hd : ∀ m n, ∃ d : RedIn (O := OK l K) (Y.γ n) (Y.κ n) (S.L m).γ l n,
      ∀ x, d.ρ (Y.c n x) = Ideal.Quotient.mk _ ((S.L m).lam (e x))) : Nonempty (LvSys Y sΛ sn sC c) :=
  ⟨{ L := fun m => hb.lv (hS.lev m) (hd m)
     dn := fun m =>
      { le := Nat.le_succ _
        sA := S.dA m
        sB := S.dB m
        dpA := hS.ddp m
        dpB := hS.ddpB m
        oA := hS.dO m
        oB := hS.dK m
        ι := hS.dι m
        lam := fun x => hS.dlam m (e x)
        cris := fun _ _ => rfl
        θ := fun b => by
          obtain ⟨x, rfl⟩ := (hS.lev (m + 1)).toB_surj b
          change hb.θ (hS.lev m) (S.dB m ((S.L (m + 1)).toB x)) = hb.θ (hS.lev (m + 1)) ((S.L (m + 1)).toB x)
          rw [hS.dB_toB, hb.θ_toB, hb.θ_toB]
        cB := 1
        t := by
          change S.dB m ((S.L (m + 1)).ι ((S.L (m + 1)).lam (e Y.t))) = 1 * (S.L m).ι ((S.L m).lam (e Y.t))
          rw [hS.dι, hS.dlam, one_mul]
        θc := map_one _ }
     gal := fun m g => (hb.gal (hS.lev m) (hd m) g).some }⟩

end CrystallineSemistableComparison.HT
