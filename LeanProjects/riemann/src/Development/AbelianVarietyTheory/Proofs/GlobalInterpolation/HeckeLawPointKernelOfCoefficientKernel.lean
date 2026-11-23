import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvSmulMemOfRedL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms

noncomputable section

namespace GlobalTheory.LvT.Built.UK

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Pts
open Formalism.HermitianLatticesTheory (localization₂)

section Corr

variable {q : ℕ} {F : Type} [Field F] {Lc Lc' : LocF q F} {n : ℕ} (e : Lc'.K ≃+* Lc.K)

def Corr (p : LocF.PP Lc n) (r : LocF.PP Lc' n) : Prop :=
  ∀ x : Fin n → Lc'.K, ((fun a => e (x a)) ∈ p.1.L ↔ x ∈ r.1.L) ∧ p.1.f (fun a => e (x a)) = r.1.f x

variable {e}

theorem vec_surj (e : Lc'.K ≃+* Lc.K) (y : Fin n → Lc.K) : ∃ x : Fin n → Lc'.K, y = fun a => e (x a) :=
  ⟨fun a => e.symm (y a), funext fun a => (e.apply_symm_apply _).symm⟩

theorem Corr.eq_iff {p p' : LocF.PP Lc n} {r r' : LocF.PP Lc' n} (h : Corr e p r) (h' : Corr e p' r') : p = p' ↔ r = r' := by
  constructor
  · rintro rfl
    exact pp_ext (fun x => (h x).1.symm.trans (h' x).1) fun x _ => (h x).2.symm.trans (h' x).2
  · rintro rfl
    refine pp_ext (fun y => ?_) fun y _ => ?_
    · obtain ⟨x, rfl⟩ := vec_surj e y
      exact (h x).1.trans (h' x).1.symm
    · obtain ⟨x, rfl⟩ := vec_surj e y
      exact (h x).2.trans (h' x).2.symm

theorem Corr.inc_iff {p p' : LocF.PP Lc n} {r r' : LocF.PP Lc' n} (h : Corr e p r) (h' : Corr e p' r') :
    p.Inc p' ↔ r.Inc r' := by
  have hk : ∀ x : Fin n → Lc'.K, (fun a => e (x a)) ∈ p'.ker ↔ x ∈ r'.ker := fun x =>
    and_congr (h' x).1 (by rw [(h' x).2])
  have hs : ∀ x : Fin n → Lc'.K, ((q : Lc.K)⁻¹ • fun a => e (x a)) = fun a => e (((q : Lc'.K)⁻¹ • x) a) := fun x => by
    funext a
    simp
  have key : ∀ x : Fin n → Lc'.K, (p.1.f (fun a => e (x a)) = 1 ∧ p.IsUp (fun a => e (x a)) p') ↔ (r.1.f x = 1 ∧ r.IsUp x r') := by
    intro x
    unfold LocF.PP.IsUp
    rw [(h x).2, (h x).1, hs, (h' _).2]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
    constructor
    · intro hh
      ext z
      rw [← hk, hh]
      exact (h z).1
    · intro hh
      ext y
      obtain ⟨z, rfl⟩ := vec_surj e y
      rw [hk, hh]
      exact (h z).1.symm
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := vec_surj e y
    exact ⟨x, (key x).1 hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, (key x).2 hx⟩

end Corr

section Step

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem tAt (sp : Split A T) : TAt T ST :=
  ⟨fun P => ⟨sp.T_mem P.1 P.2, sp.T_nsq P.1 P.2⟩, fun P Q => sp.nonconj P.1 P.2 Q.1 Q.2⟩

theorem eq_of_pair (sp : Split A T) (ht : A.Tied T) {b : S.β} {d d' : S.D b} (ho : (sp.off b).r d d')
    (hp : ∀ P, pair ((tAt sp).unif P) _ (ht.ok b d) = pair ((tAt sp).unif P) _ (ht.ok b d')) : d = d' :=
  sp.ext b d d' ho (deco_ext (tAt sp) (ht.ok b d) (ht.ok b d')
    (fun w hw => sp.off_lat b d d' ho w fun P hP => hw ⟨P, hP⟩) hp)

theorem pair_eq_of_deco {P : ST} (h : Unif T P.1) {d d' : Deco E n ST ∅} (hd : d.Ok) (e : d = d') :
    pair h d hd = pair h d' (e ▸ hd) := by subst e; rfl

theorem above_off (sp : Split A T) {b : S.β} {P : ST} {d d₁ : S.D b} (h : Above A b P d d₁) : (sp.off b).r d d₁ := by
  obtain ⟨x, hx, hf, rfl⟩ := h
  exact sp.off_up b d P x hx hf

theorem above_iff (sp : Split A T) (ht : A.Tied T) {b : S.β} (P : ST) {d d₁ : S.D b} (ho : (sp.off b).r d d₁) :
    Above A b P d d₁ ↔
      (∀ Q, Q ≠ P → pair ((tAt sp).unif Q) _ (ht.ok b d₁) = pair ((tAt sp).unif Q) _ (ht.ok b d)) ∧
      (pair ((tAt sp).unif P) _ (ht.ok b d)).Inc (pair ((tAt sp).unif P) _ (ht.ok b d₁)) := by
  have h := tAt sp
  have hd := ht.ok b d
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    have e := ht.up_deco b d P x hx hf
    refine ⟨fun Q hQ => ?_, ?_⟩
    · rw [pair_eq_of_deco _ _ e]
      exact pair_up_ne h hd hQ hx _
    · rw [pair_eq_of_deco _ (ht.ok b (A.up b d P x)) e]
      refine ⟨x, hf, le_locP _ _ hx, ?_, ?_⟩
      · ext y
        rw [mem_pair_ker _ (h.ne P), hd.dnN_up P (h.move P) (h.unif P).mem (h.unif P).nsq hx hf]
        rfl
      · have := hd.up_f_inv P (h.move P) (h.unif P).mem (h.unif P).nsq hx hf
        rw [map_natCast] at this
        exact this
  · rintro ⟨h1, x, hf, hp⟩
    have hx : x ∈ localization₂ P.1.asIdeal (A.N b d) := hp.1
    obtain ⟨x', hx', hr⟩ := redL_surj (redL (A.N b d) P.1 x)
    have hx'' : x' ∈ localization₂ P.1.asIdeal (A.N b d) := le_locP _ _ hx'
    have hf' : A.f b d P x' = 1 := by
      have hneg : (-1 : GlobalTheory.LvT.Inh.valO P.1) • x ∈ localization₂ P.1.asIdeal (A.N b d) := (locO P.1 _).smul_mem _ hx
      have h0 : redL (A.N b d) P.1 (x' + (-1 : GlobalTheory.LvT.Inh.valO P.1) • x) = 0 := by
        rw [redL_add hx'' hneg, redL_smul _ hx, hr, map_neg, map_one, neg_one_smul, add_neg_cancel]
      have h2 := inv_smul_mem_of_redL (h.unif P) ((localization₂ _ _).add_mem hx'' hneg) h0
      have h3 := hd.f_smul P (T : 𝓞 E) _ h2
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (h.unif P).mem, zero_mul, ← algebraMap_smul E (T : 𝓞 E), map_natCast,
        smul_inv_smul₀ (h.unif P).ne_zero] at h3
      have e : x' = (x' + (-1 : GlobalTheory.LvT.Inh.valO P.1) • x) + x := by rw [neg_one_smul]; abel
      have h4 := hd.f_add P _ ((localization₂ _ _).add_mem hx'' hneg) _ hx
      rw [← e, h3, zero_add] at h4
      exact h4.trans hf
    refine ⟨x', hx', hf', ?_⟩
    have e := ht.up_deco b d P x' hx' hf'
    refine eq_of_pair sp ht ((sp.off b).trans ((sp.off b).symm ho) (sp.off_up b d P x' hx' hf')) fun Q => ?_
    rw [pair_eq_of_deco _ (ht.ok b (A.up b d P x')) e]
    by_cases hQ : Q = P
    · subst hQ
      exact (pair_up h hd Q hx' hf' hr hp _).symm
    · rw [h1 Q hQ]
      exact (pair_up_ne h hd hQ hx' _).symm

end Step

section Real

variable {D : D7} {u : D.what₂.Word} {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}
  (R : B.Real i sp M)

theorem corr_pt (b : (B.I.S i).β) (d : (B.I.S i).D b) (P : B.ch.A.vT) :
    Corr (Lc := M.Lc P) (Lc' := locF ((tAt sp).unif (B.pr P))) (R.iK P) ((R.pt b d).2 P)
      (pair ((tAt sp).unif (B.pr P)) _ ((B.hJ.tied i).ok b d)) :=
  fun x => ⟨R.pt_L b d P x, R.pt_f b d P x⟩

theorem fst_of_off {b : (B.I.S i).β} {d d' : (B.I.S i).D b} (h : (sp.off b).r d d') : (R.pt b d).1 = (R.pt b d').1 := by
  have := (R.fst 1 b d d').2 ⟨1, map_one _, map_one _, by rwa [one_smul]⟩
  rwa [map_one, one_smul] at this

theorem exists_pt {b : (B.I.S i).β} (d : (B.I.S i).D b) {p : M.Pt} (h : p.1 = (R.pt b d).1) :
    ∃ d', (sp.off b).r d' d ∧ p = R.pt b d' := by
  obtain ⟨ζ, b₁, d₁, rfl⟩ := R.surj p
  obtain rfl := R.idx ζ b₁ b d₁ d h
  obtain ⟨g, h1, h2, h3⟩ := (R.fst ζ b₁ d₁ d).1 h
  exact ⟨_, h3, (R.inj ζ b₁ d₁ _).2 ⟨g, h1, h2, rfl⟩⟩

theorem pt_inj {b : (B.I.S i).β} {d d' : (B.I.S i).D b} (ho : (sp.off b).r d d') (h : R.pt b d = R.pt b d') : d = d' :=
  eq_of_pair sp (B.hJ.tied i) ho fun (P : B.ch.A.vT) =>
    ((corr_pt R b d P).eq_iff (corr_pt R b d' P)).1 (by rw [h])

theorem inc_iff {b : (B.I.S i).β} (v : B.ch.A.vT) {d d' : (B.I.S i).D b} (ho : (sp.off b).r d d') :
    M.Inc v (R.pt b d) (R.pt b d') ↔ Above (B.J.A i) b (B.pr v) d d' := by
  rw [above_iff sp (B.hJ.tied i) (B.pr v) ho]
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨fun (Q : B.ch.A.vT) hQ => ((corr_pt R b d' Q).eq_iff (corr_pt R b d Q)).1 (h2 Q hQ),
      ((corr_pt R b d v).inc_iff (corr_pt R b d' v)).1 h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨(fst_of_off R ho).symm, fun Q hQ => ((corr_pt R b d' Q).eq_iff (corr_pt R b d Q)).2 (h2 Q hQ),
      ((corr_pt R b d v).inc_iff (corr_pt R b d' v)).2 h3⟩

theorem above_image (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {p₁ | M.Inc v (g • R.pt b d) p₁} = (fun d₁ => g • R.pt b d₁) '' {d₁ | Above (B.J.A i) b (B.pr v) d d₁} := by
  have hs := (inc_finite_stable D u _ i M v).2.1
  ext p₁
  constructor
  · intro h
    have h' := (hs g⁻¹ _ _).1 h
    rw [inv_smul_smul] at h'
    obtain ⟨d', ho, e⟩ := exists_pt R d h'.1
    rw [e] at h'
    exact ⟨d', (inc_iff R v ((sp.off b).symm ho)).1 h', by beta_reduce; rw [← e, smul_inv_smul]⟩
  · rintro ⟨d', h, rfl⟩
    exact (hs g _ _).1 ((inc_iff R v (above_off sp h)).2 h)

theorem below_image (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {p₀ | M.Inc v p₀ (g • R.pt b d)} = (fun d₀ => g • R.pt b d₀) '' {d₀ | Above (B.J.A i) b (B.pr v) d₀ d} := by
  have hs := (inc_finite_stable D u _ i M v).2.1
  ext p₀
  constructor
  · intro h
    have h' := (hs g⁻¹ _ _).1 h
    rw [inv_smul_smul] at h'
    obtain ⟨d', ho, e⟩ := exists_pt R d h'.1.symm
    rw [e] at h'
    exact ⟨d', (inc_iff R v ho).1 h', by beta_reduce; rw [← e, smul_inv_smul]⟩
  · rintro ⟨d', h, rfl⟩
    exact (hs g _ _).1 ((inc_iff R v (above_off sp h)).2 h)

theorem above_injOn (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    Set.InjOn (fun d₁ => g • R.pt b d₁) {d₁ | Above (B.J.A i) b (B.pr v) d d₁} := fun _ h _ h' e =>
  pt_inj R ((sp.off b).trans ((sp.off b).symm (above_off sp h)) (above_off sp h')) (MulAction.injective g e)

theorem below_injOn (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    Set.InjOn (fun d₀ => g • R.pt b d₀) {d₀ | Above (B.J.A i) b (B.pr v) d₀ d} := fun _ h _ h' e =>
  pt_inj R ((sp.off b).trans (above_off sp h) ((sp.off b).symm (above_off sp h'))) (MulAction.injective g e)

include R in
theorem above_finite {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {d₁ | Above (B.J.A i) b (B.pr v) d d₁}.Finite :=
  Set.Finite.of_finite_image (above_image R 1 v d ▸ ((inc_finite_stable D u _ i M v).1 _).1) (above_injOn R 1 v d)

include R in
theorem below_finite {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {d₀ | Above (B.J.A i) b (B.pr v) d₀ d}.Finite :=
  Set.Finite.of_finite_image (below_image R 1 v d ▸ ((inc_finite_stable D u _ i M v).1 _).2) (below_injOn R 1 v d)

include R in
theorem val_ext {W : Type} [AddCommGroup W] [Module ℂ W] (f g : M.Val →ₗ[ℂ] W)
    (h : ∀ (F : B.V i) (y : M.Val), y.1 = B.ev i F → f y = g y) : f = g := by
  have hv : M.Val = Submodule.span ℂ (Set.range (B.ev i)) :=
    R.val_eq.trans (span_evV B.emb 1 (B.lam i) D.what₂.embLL).symm
  ext ⟨y, hy⟩
  have key : ∀ y ∈ Submodule.span ℂ (Set.range (B.ev i)), ∀ hy : y ∈ M.Val, f ⟨y, hy⟩ = g ⟨y, hy⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨F, rfl⟩ := hx
      exact fun hy => h F _ rfl
    | zero => exact fun hy => (map_zero f).trans (map_zero g).symm
    | add x y hx hy ihx ihy =>
      intro hxy
      have hx' : x ∈ M.Val := hv ▸ hx
      have hy' : y ∈ M.Val := hv ▸ hy
      exact (map_add f ⟨x, hx'⟩ ⟨y, hy'⟩).trans ((congrArg₂ (· + ·) (ihx hx') (ihy hy')).trans (map_add g _ _).symm)
    | smul c x hx ih =>
      intro hc
      have hx' : x ∈ M.Val := hv ▸ hx
      exact (map_smul f c ⟨x, hx'⟩).trans ((congrArg (c • ·) (ih hx')).trans (map_smul g c _).symm)
  exact key y (hv ▸ hy) hy

end Real

theorem ukLaw_of_kerUK (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T)
    (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M)
    (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M') (ht : K.TgtEq) (hk : Built.Dat.KerIs R R' K k)
    (hu : Built.Dat.KerUK k) : K.UKLaw := by
  intro v p p' y
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  generalize R.zeta ζ = g
  generalize R'.zeta ζ' = g'
  obtain ⟨y, rfl⟩ : ∃ y₀, y = M.act g y₀ :=
    ⟨M.act g⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  have f1 := above_finite R' v d'
  have f0 := below_finite R v d
  rw [above_image R' g' v d', below_image R g v d, finsum_mem_image (above_injOn R' g' v d'),
    finsum_mem_image (below_injOn R g v d), finsum_mem_eq_finite_toFinset_sum _ f1, finsum_mem_eq_finite_toFinset_sum _ f0]
  simp only [K.src, ht g']
  rw [← map_sum, ← map_sum, ← map_smul]
  congr 1
  have := val_ext R (∑ d₁ ∈ f1.toFinset, K.k (R.pt b d) (R'.pt b' d₁))
    (((B.ch.A.T : ℂ) ^ ((D.R.t + 1) / 2)) • ∑ d₀ ∈ f0.toFinset, K.k (R.pt b d₀) (R'.pt b' d')) (fun F y hy => ?_)
  · simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using LinearMap.congr_fun this y
  have h := hu b b' d d' (B.pr v) F
  rw [finsum_mem_eq_finite_toFinset_sum _ f1, finsum_mem_eq_finite_toFinset_sum _ f0] at h
  have h2 := congrArg (evV B.emb (1 : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) B.E) (B.lam (i + 1)) D.what₂.embLL) h
  rw [LinearMap.map_smulₛₗ, map_sum, map_sum, map_pow, map_natCast] at h2
  apply Subtype.ext
  rw [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul, Submodule.coe_sum, Submodule.coe_sum,
    Finset.sum_congr rfl fun d₁ _ => hk b b' d d₁ F y hy, Finset.sum_congr rfl fun d₀ _ => hk b b' d₀ d' F y hy]
  exact h2

end GlobalTheory.LvT.Built.UK
