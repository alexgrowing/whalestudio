import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

open MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.ModuliGenus

theorem exists_eq_nsmul_of_primes {L : Type} [AddCommGroup L] (n : ℕ) (x : L)
    (h : ∀ p : ℕ, p.Prime → ∃ m : ℕ, ¬ p ∣ m ∧ ∃ e, m • x = n • e) : ∃ e, x = n • e := by
  let N : AddSubgroup L := (nsmulAddMonoidHom n : L →+ L).range
  have hm : ∀ k : ℕ, (∃ e, k • x = n • e) ↔ addOrderOf (QuotientAddGroup.mk' N x) ∣ k := fun k => by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    exact exists_congr fun e => eq_comm
  have h1 : addOrderOf (QuotientAddGroup.mk' N x) = 1 := by
    by_contra h1
    obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨m, hpm, he⟩ := h p hp
    exact hpm (hd.trans ((hm m).1 he))
  simpa using (hm 1).2 (by rw [h1])

theorem exists_crt {M : Type} [AddCommGroup M] (k : ℕ → ℕ) (f : ℕ → M) (v : ℕ → ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hk : ∀ p ∈ S, (k p).Coprime p) :
    ∃ g : M, ∀ p ∈ S, ∃ e, k p • g = f p + p ^ v p • e := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q S hq ih =>
    obtain ⟨g, hg⟩ := ih (fun p hp => hS p (Finset.mem_insert_of_mem hp)) fun p hp => hk p (Finset.mem_insert_of_mem hp)
    have hc : (k q * ∏ p ∈ S, p ^ v p).Coprime (q ^ v q) := by
      refine Nat.Coprime.pow_right _ (Nat.Coprime.mul_left (hk q (Finset.mem_insert_self _ _)) ?_)
      refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.pow_left _ ?_
      exact (Nat.coprime_primes (hS p (Finset.mem_insert_of_mem hp)) (hS q (Finset.mem_insert_self _ _))).2
        fun e => hq (e ▸ hp)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
    refine ⟨g + (∏ p ∈ S, p ^ v p) • a • (f q - k q • g), fun p hp => ?_⟩
    rcases Finset.mem_insert.1 hp with rfl | hp
    · refine ⟨-(b • (f p - k p • g)), ?_⟩
      have h1 := congrArg (fun t : ℤ => t • (f p - k p • g)) hab
      simp only [add_smul, one_smul, mul_comm a, mul_comm b, mul_smul, natCast_zsmul] at h1
      rw [smul_add, smul_neg, eq_sub_of_add_eq h1]
      abel
    · obtain ⟨e, he⟩ := hg p hp
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p => p ^ v p) hp
      refine ⟨e + k p • c • a • (f q - k q • g), ?_⟩
      rw [smul_add, he, hc, smul_add, mul_smul, smul_comm (k p), add_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_eq_nsmul_of_dvd (D : Datum H) {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) :
    ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

theorem exists_system (D D' : Datum H) (hp : D'.p = D.p) (hq : D'.q = D.q) :
    ∃ g : ℕ → D.La →ₗ[𝓞 E] D'.La,
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e) ∧
      ∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ D'.EF (g n a) (g n b) - D.EF a b := by
  have h1 : ∀ p : ℕ, ∃ (k : ℕ) (f : D.La →ₗ[𝓞 E] D'.La), p.Prime →
      k.Coprime p ∧ ∀ x y, D'.EF (f x) (f y) = (k : ℤ) ^ 2 * D.EF x y := fun p => by
    by_cases h : p.Prime
    · obtain ⟨k, f, hf⟩ := GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry E H D D' hp hq p h.pos
      exact ⟨k, f, fun _ => hf⟩
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose k f hf using h1
  have h2 : ∀ n : ℕ, ∃ g : D.La →ₗ[𝓞 E] D'.La, ∀ p : ℕ, p.Prime → ∀ a, ∃ e,
      k p • g a = f p a + p ^ n.factorization p • e := fun n => by
    obtain ⟨g, hg⟩ := exists_crt k f n.factorization n.primeFactors (fun p => Nat.prime_of_mem_primeFactors)
      fun p hp => (hf p (Nat.prime_of_mem_primeFactors hp)).1
    refine ⟨g, fun p hp a => ?_⟩
    by_cases h : p ∈ n.primeFactors
    · obtain ⟨e, he⟩ := hg p h
      exact ⟨e a, LinearMap.congr_fun he a⟩
    · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at h
      exact ⟨k p • g a - f p a, by simp [h]⟩
  choose g hg using h2
  have hnd : ∀ n p j : ℕ, 0 < n → p.Prime → ¬ p ∣ ordCompl[p] n * k p ^ j := fun n p j hn hp h => by
    rcases (hp.dvd_mul).1 h with h | h
    · exact Nat.not_dvd_ordCompl hp hn.ne' h
    · exact (hp.coprime_iff_not_dvd.1 (hf p hp).1.symm) (hp.dvd_of_dvd_pow h)
  refine ⟨g, fun n m hn hm a => ?_, fun n hn a b => ?_⟩
  · simp_rw [← sub_eq_iff_eq_add']
    refine exists_eq_nsmul_of_primes n _ fun p hp => ⟨_, hnd n p 1 hn hp, ?_⟩
    obtain ⟨e, he⟩ := hg n p hp a
    obtain ⟨e', he'⟩ := hg (n * m) p hp a
    rw [Nat.factorization_mul hn.ne' hm.ne', Finsupp.add_apply, pow_add, mul_smul] at he'
    refine ⟨p ^ m.factorization p • e' - e, ?_⟩
    rw [pow_one, mul_smul, smul_sub, he, he', add_sub_add_left_eq_sub, ← smul_sub, smul_smul, mul_comm,
      Nat.ordProj_mul_ordCompl_eq_self]
  · have := exists_eq_nsmul_of_primes n (D'.EF (g n a) (g n b) - D.EF a b) fun p hp => ⟨_, hnd n p 2 hn hp, ?_⟩
    · obtain ⟨e, he⟩ := this
      exact ⟨e, by rw [he, nsmul_eq_mul]⟩
    obtain ⟨e, he⟩ := hg n p hp a
    obtain ⟨e', he'⟩ := hg n p hp b
    have h3 := congrArg₂ (fun x y => D'.EF x y) he he'
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, (hf p hp).2, nsmul_eq_mul] at h3
    refine ⟨D'.EF e (f p b) + D'.EF (f p a) e' + (p ^ n.factorization p : ℕ) * D'.EF e e', ?_⟩
    have h4 : ((p ^ n.factorization p : ℕ) : ℤ) * (ordCompl[p] n : ℕ) = n := by
      exact_mod_cast Nat.ordProj_mul_ordCompl_eq_self n p
    simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow (k p)]
    rw [← h4]
    linear_combination ((ordCompl[p] n : ℕ) : ℤ) * h3

theorem surj_mod (D D' : Datum H) {n : ℕ} (hn : 0 < n) (g : D.La →ₗ[𝓞 E] D'.La) (g' : D'.La →ₗ[𝓞 E] D.La)
    (hg : ∀ a, (∃ e, g a = n • e) → ∃ e, a = n • e) (hg' : ∀ a, (∃ e, g' a = n • e) → ∃ e, a = n • e) (a' : D'.La) :
    ∃ a e, a' = g a + n • e := by
  have := D'.fin
  let N : Submodule (𝓞 E) D'.La := LinearMap.range (n • LinearMap.id)
  have hN : ∀ x, x ∈ N ↔ ∃ e, x = n • e := fun x => exists_congr fun e => eq_comm
  have hle : N ≤ N.comap (g ∘ₗ g') := fun x hx => by
    obtain ⟨e, rfl⟩ := (hN x).1 hx
    exact (hN _).2 ⟨_, map_nsmul _ _ _⟩
  have : Module.Finite ℤ (D'.La ⧸ N) := Module.Finite.trans (𝓞 E) _
  have : Finite (D'.La ⧸ N) := Module.finite_of_fg_torsion _ fun x => by
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    change (n : ℤ) • N.mkQ y = 0
    rw [natCast_zsmul, ← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hN _).2 ⟨_, rfl⟩
  have hi : Function.Injective (N.mapQ N _ hle) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hN _).2 (hg' _ (hg _ ((hN _).1 hx)))
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hi (N.mkQ a')
  obtain ⟨y, rfl⟩ := N.mkQ_surjective x
  rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq] at hx
  obtain ⟨e, he⟩ := (hN _).1 hx
  exact ⟨g' y, e, sub_eq_iff_eq_add'.1 he⟩

structure IsTower {D D' : Datum H} (g : ℕ → D.La →ₗ[𝓞 E] D'.La) : Prop where
  tower : ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, g (n * m) a = g n a + n • e
  isom : ∀ n : ℕ, 0 < n → ∀ a b, (n : ℤ) ∣ D'.EF (g n a) (g n b) - D.EF a b
  surj : ∀ n : ℕ, 0 < n → ∀ a', ∃ a e, a' = g n a + n • e

theorem isTower_id (D : Datum H) : IsTower (D := D) (D' := D) fun _ => LinearMap.id :=
  ⟨fun _ _ _ _ _ => ⟨0, by simp⟩, fun _ _ _ _ => by simp, fun _ _ a => ⟨a, 0, by simp⟩⟩

theorem inj_mod {D D' : Datum H} {n : ℕ} (hn : 0 < n) (g : D.La →ₗ[𝓞 E] D'.La)
    (hg : ∀ a b, (n : ℤ) ∣ D'.EF (g a) (g b) - D.EF a b) (a : D.La) (h : ∃ e, g a = n • e) : ∃ e, a = n • e := by
  obtain ⟨e, he⟩ := h
  refine exists_eq_nsmul_of_dvd D hn a fun b => ?_
  have h1 := hg a b
  rw [he, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h1
  exact (dvd_sub_right (dvd_mul_right _ _)).1 h1

theorem exists_isTower (D D' : Datum H) (hp : D'.p = D.p) (hq : D'.q = D.q) :
    ∃ g : ℕ → D.La →ₗ[𝓞 E] D'.La, IsTower g := by
  obtain ⟨g, h1, h2⟩ := exists_system D D' hp hq
  obtain ⟨g', -, h2'⟩ := exists_system D' D hp.symm hq.symm
  exact ⟨g, h1, h2, fun n hn => surj_mod D D' hn (g n) (g' n) (inj_mod hn _ (h2 n hn)) (inj_mod hn _ (h2' n hn))⟩

theorem IsTower.exists_inv {D D' : Datum H} {g : ℕ → D.La →ₗ[𝓞 E] D'.La} (hg : IsTower g) :
    ∃ h : ℕ → D'.La →ₗ[𝓞 E] D.La, IsTower h ∧ (∀ n, 0 < n → ∀ a, ∃ e, g n (h n a) = a + n • e) ∧
      ∀ n, 0 < n → ∀ a, ∃ e, h n (g n a) = a + n • e := by
  have h1 : ∀ n : ℕ, ∃ h : D'.La →ₗ[𝓞 E] D.La, 0 < n → ∀ a, ∃ e, g n (h a) = a + n • e := fun n => by
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    have := D'.proj
    obtain ⟨s, hs⟩ := Module.projective_lifting_property ((g n).coprod (n • LinearMap.id)) LinearMap.id fun a' => by
      obtain ⟨a, e, h⟩ := hg.surj n hn a'
      exact ⟨(a, e), h.symm⟩
    refine ⟨LinearMap.fst _ _ _ ∘ₗ s, fun _ a => ⟨-(s a).2, ?_⟩⟩
    have h2 : g n (s a).1 + n • (s a).2 = a := LinearMap.congr_fun hs a
    rw [smul_neg, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq h2
  choose h hh using h1
  have h2 : ∀ n, 0 < n → ∀ a, ∃ e, h n (g n a) = a + n • e := fun n hn a => by
    simp_rw [← sub_eq_iff_eq_add']
    refine inj_mod hn _ (hg.isom n hn) _ ?_
    simp_rw [map_sub, sub_eq_iff_eq_add']
    exact hh n hn _
  refine ⟨h, ⟨fun n m hn hm a => ?_, fun n hn a b => ?_, fun n hn a => ?_⟩, hh, h2⟩
  · simp_rw [← sub_eq_iff_eq_add']
    refine inj_mod hn _ (hg.isom n hn) _ ?_
    obtain ⟨e₁, he₁⟩ := hh n hn a
    obtain ⟨e₂, he₂⟩ := hh (n * m) (Nat.mul_pos hn hm) a
    obtain ⟨e₃, he₃⟩ := hg.tower n m hn hm (h (n * m) a)
    refine ⟨m • e₂ - e₃ - e₁, ?_⟩
    rw [map_sub, he₁, eq_sub_of_add_eq he₃.symm, he₂, smul_sub, smul_sub, mul_smul]
    abel
  · obtain ⟨e₁, he₁⟩ := hh n hn a
    obtain ⟨e₂, he₂⟩ := hh n hn b
    obtain ⟨c, hc⟩ := hg.isom n hn (h n a) (h n b)
    rw [he₁, he₂] at hc
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at hc
    exact ⟨D'.EF e₁ b + D'.EF a e₂ + n * D'.EF e₁ e₂ - c, by linear_combination -hc⟩
  · obtain ⟨e, he⟩ := h2 n hn a
    exact ⟨g n a, -e, by rw [he, smul_neg, add_neg_cancel_right]⟩

def tateComp {D D' : Datum H} {g : ℕ → D.La →ₗ[𝓞 E] D'.La} (hg : IsTower g) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D' k Q act e) : TateIso D k Q act e where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := I.ev n (g n a)
  add n a b := by rw [map_add, I.add]
  lin n c a := by rw [map_smul, I.lin]
  ker n hn a := by
    rw [I.ker n hn]
    refine ⟨inj_mod hn _ (hg.isom n hn) a, ?_⟩
    rintro ⟨b, rfl⟩
    exact ⟨_, map_nsmul _ _ _⟩
  onto n hn x := by
    rw [I.onto n hn]
    refine ⟨?_, fun ⟨a, ha⟩ => ⟨_, ha⟩⟩
    rintro ⟨a', rfl⟩
    obtain ⟨a, c, rfl⟩ := hg.surj n hn a'
    exact ⟨a, by rw [I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]⟩
  tower n m hn hm a := by
    obtain ⟨c, hc⟩ := hg.tower n m hn hm a
    rw [I.tower n m hn hm, hc, I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]
  isom n hn a b := by
    have h := ((I.ζ_prim n hn).zpow_eq_one_iff_dvd _).2 (hg.isom n hn a b)
    rw [zpow_sub, mul_inv_eq_one] at h
    rw [← h]
    exact I.isom n hn _ _

theorem map_mem_smul_top {D D' : Datum H} (g : D.La →ₗ[𝓞 E] D'.La) (J : Ideal (𝓞 E)) (a : D.La)
    (ha : a ∈ J • (⊤ : Submodule (𝓞 E) D.La)) : g a ∈ J • (⊤ : Submodule (𝓞 E) D'.La) := by
  have h := Submodule.mem_map_of_mem (f := g) ha
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

def objComp {D D' : Datum H} (hp : D'.p = D.p) (hq : D'.q = D.q) {g : ℕ → D.La →ₗ[𝓞 E] D'.La} (hg : IsTower g)
    (o : Obj D' l b s) : Obj D l b s where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta a := o.eta (g l.M a)
  eta_add a c := by rw [map_add, o.eta_add]
  eta_ker a ha := o.eta_ker _ (map_mem_smul_top _ _ a ha)
  etaA a := o.etaA (g l.A a)
  etaA_add a c := by rw [map_add, o.etaA_add]
  etaA_ker a := by rw [map_nsmul, o.etaA_ker]
  geom k _ _ x β hx := by
    obtain ⟨h1, I, h2, h3, h4⟩ := o.geom k x β hx
    refine ⟨?_, tateComp hg I, h2, fun a => h3 _, fun a ha => h4 _ (map_mem_smul_top _ _ a ha)⟩
    unfold DetCond at h1 ⊢
    rwa [← hp, ← hq]

theorem eta_add_nsmul {D : Datum H} (o : Obj D l b s) (a e : D.La) : o.eta (a + l.M • e) = o.eta a := by
  rw [o.eta_add, o.eta_ker (l.M • e), _root_.mul_one]
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  refine Submodule.smul_mem_smul (Ideal.mul_le_left (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ?_) trivial
  rw [l.prod]
  exact Ideal.mem_span_singleton_self _

theorem etaA_add_nsmul {D : Datum H} (o : Obj D l b s) (a e : D.La) : o.etaA (a + l.A • e) = o.etaA a := by
  rw [o.etaA_add, o.etaA_ker, _root_.mul_one]

theorem objMap_iff {D D' : Datum H} (hp : D'.p = D.p) (hq : D'.q = D.q) {g : ℕ → D.La →ₗ[𝓞 E] D'.La}
    {h : ℕ → D'.La →ₗ[𝓞 E] D.La} (hg : IsTower g) (hh : IsTower h)
    (h1 : ∀ n, 0 < n → ∀ a, ∃ e, g n (h n a) = a + n • e) (h2 : ∀ n, 0 < n → ∀ a, ∃ e, h n (g n a) = a + n • e)
    {S' : Scheme.{0}} {s' : S' ⟶ Sp B} (o : Obj D l b s') (u : Obj D' l b s) (f : S' ⟶ S) :
    Nonempty (ObjMap o (objComp hp hq hg u) f) ↔ Nonempty (ObjMap (objComp hp.symm hq.symm hh o) u f) := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨fun ⟨m⟩ => ⟨⟨m.toSABMap, fun a => ?_, fun a => ?_⟩⟩, fun ⟨m⟩ => ⟨⟨m.toSABMap, fun a => ?_, fun a => ?_⟩⟩⟩
  · obtain ⟨e, he⟩ := h1 _ hM a
    rw [← eta_add_nsmul u a e, ← he]
    exact m.eta _
  · obtain ⟨e, he⟩ := h1 _ l.A_pos a
    rw [← etaA_add_nsmul u a e, ← he]
    exact m.etaA _
  · obtain ⟨e, he⟩ := h2 _ hM a
    rw [← eta_add_nsmul o a e, ← he]
    exact m.eta _
  · obtain ⟨e, he⟩ := h2 _ l.A_pos a
    rw [← etaA_add_nsmul o a e, ← he]
    exact m.etaA _

theorem exists_moduli_of_signature_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw Dw' : Datum H) (l : Level H) (Xo : Moduli Dw l), Dw.p = Dw'.p → Dw.q = Dw'.q →
    ∃ (Xo' : Moduli Dw' l) (_ : Xo'.X = Xo.X), HEq Xo'.s Xo.s ∧ HEq Xo'.univ.t Xo.univ.t := by
  intro E _ _ _ H D D' l Xo hp hq
  obtain ⟨g, hg⟩ := exists_isTower D' D hp hq
  obtain ⟨h, hh, h1, h2⟩ := hg.exists_inv
  have hd : D'.dim = D.dim := by rw [Datum.dim, Datum.dim, hp, hq]
  refine ⟨⟨Xo.X, Xo.s, Xo.qproj, hd ▸ Xo.smooth, objComp hp hq hg Xo.univ, fun S s' hS o => ?_, fun k _ x o m m' => ?_⟩,
    rfl, HEq.rfl, HEq.rfl⟩
  · simp only [objMap_iff hp hq hg hh h1 h2]
    exact Xo.rep S s' hS _
  · rw [objMap_iff hp hq hg hh h1 h2] at m m'
    exact Xo.unram k x _ m m'

end GlobalTheory.ModuliGenus
