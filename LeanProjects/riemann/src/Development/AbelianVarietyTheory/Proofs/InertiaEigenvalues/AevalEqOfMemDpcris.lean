import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPolyPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InerDecomp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootsOfUnityCharacterHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtendCharacterTrivialOnNormal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPoly
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial

noncomputable section
namespace GlobalTheory.InertiaChars

theorem IK_le_iner : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'), IK K ≤ (pc P h hN hF hS).Iner := by
  intro l _ P K K' h hN hF hS g hg c
  have hfix := GlobalTheory.BKGal.UnitModel.fix_Kur hg
  have hc : (c : Om l) ∈ MaximalUnramifiedExtension l := (IntermediateField.mem_inf.1 c.2).2
  show (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c
  rw [P.PD_actB]
  exact P.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix c hc)

theorem coprime_orderOf : ∀ (l : ℕ) [Fact l.Prime] {F : Type} [Field F] [CharP F l] (y : Fˣ) (n : ℕ), 0 < n → y ^ n = 1 → Nat.Coprime (orderOf y) l := by
  intro l hl F _ _ y n hn hy
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl.out]
  rintro ⟨M, hM⟩
  have hpos : 0 < orderOf y := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hy⟩)
  have hz : (y ^ M) ^ l = 1 := by rw [← pow_mul, mul_comm, ← hM, pow_orderOf_eq_one]
  have h1 : ((y ^ M : Fˣ) : F) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  have h2 : (((y ^ M : Fˣ) : F) - 1) ^ l = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
  have h3 : ((y ^ M : Fˣ) : F) = 1 := sub_eq_zero.1 (pow_eq_zero_iff hl.out.ne_zero |>.1 h2)
  have hz1 : y ^ M = 1 := Units.ext h3
  have hMpos : 0 < M := Nat.pos_of_mul_pos_left (hM ▸ hpos)
  have hdvd := Nat.le_of_dvd hMpos (orderOf_dvd_of_pow_eq_one hz1)
  have hl2 := hl.out.two_le
  rw [hM] at hdvd
  nlinarith

theorem exists_gen : ∀ {G F : Type} [Group G] [Field F] (I : Subgroup G) (c : ↥I →* Fˣ) (n : ℕ), 0 < n → (∀ g, c g ^ n = 1) → ∀ (Sig : Finset (↥I →* Fˣ)), (∀ a ∈ Sig, ∃ k : ℕ, ∀ g, a g = c g ^ k) → ∃ γ : ↥I, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : ↥I, ∃ (m : ℕ) (u : ↥I), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ m * u := by
  intro G F _ _ I c n hn hc Sig hSig
  haveI : NeZero n := ⟨hn.ne'⟩
  have hle : c.range ≤ rootsOfUnity n F := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact hc g
  haveI : Finite c.range := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  haveI : IsCyclic c.range := isCyclic_of_subgroup_isDomain ((Units.coeHom F).comp c.range.subtype)
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := c.range)
  obtain ⟨γ, hγ⟩ := x.2
  have hgen : ∀ g, ∃ m : ℕ, c g = c γ ^ m := by
    intro g
    obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hx ⟨c g, g, rfl⟩)
    refine ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    rw [SubmonoidClass.coe_pow, ← hγ] at this
    exact this.symm
  refine ⟨γ, fun a ha b hb hab => ?_, fun g => ?_⟩
  · obtain ⟨ka, hka⟩ := hSig a ha
    obtain ⟨kb, hkb⟩ := hSig b hb
    ext1 g
    obtain ⟨m, hm⟩ := hgen g
    rw [hka g, hkb g, hm, ← pow_mul, ← pow_mul, mul_comm m ka, mul_comm m kb, pow_mul, pow_mul, ← hka γ,
      ← hkb γ, hab]
  · obtain ⟨m, hm⟩ := hgen g
    refine ⟨m, (γ ^ m)⁻¹ * g, fun a ha => ?_, by rw [mul_inv_cancel_left]⟩
    obtain ⟨k, hk⟩ := hSig a ha
    rw [hk, map_mul, map_inv, map_pow, hm, inv_mul_cancel, one_pow]

open TensorProduct

section Helpers
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_mul (g g' : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * g') x = actVB PD ρ g (actVB PD ρ g' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actVB_one (x : V ⊗[Qp] B) : actVB PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem actVB_pow (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    actVB PD ρ (g ^ n) x = (actVB PD ρ g ^ n) x := by
  induction n with
  | zero => simp [actVB_one]
  | succ n ih => rw [pow_succ', actVB_mul, ih, pow_succ', Module.End.mul_apply]

theorem aeval_actVB (g : G) (q : LL[X]) {N : ℕ} (hN : q.natDegree < N) (x : V ⊗[Qp] B) :
    (aeval (actVB PD ρ g) q) x = ∑ n ∈ Finset.range N, q.coeff n • actVB PD ρ (g ^ n) x := by
  rw [aeval_eq_sum_range' hN, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, actVB_pow]

end Helpers

theorem aeval_eq_of_mem_Dpcris {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (g s : G) (hgs : s⁻¹ * g ∈ PC.H) (q : LL[X]) (x : V ⊗[Qp] B)
    (hx : x ∈ PC.Dpcris ρ) :
    (aeval (actVB PC.PD ρ g) q) x = (aeval (actVB PC.PD ρ s) q) x := by
  have hpow : ∀ n : ℕ, actVB PC.PD ρ (g ^ n) x = actVB PC.PD ρ (s ^ n) x ∧
      actVB PC.PD ρ (s ^ n) x ∈ PC.Dpcris ρ := by
    intro n
    induction n with
    | zero => exact ⟨by rw [pow_zero, pow_zero], by rw [pow_zero, actVB_one]; exact hx⟩
    | succ n ih =>
      have hy := ih.2
      have e1 : actVB PC.PD ρ g (actVB PC.PD ρ (s ^ n) x) = actVB PC.PD ρ s (actVB PC.PD ρ (s ^ n) x) := by
        rw [show g = s * (s⁻¹ * g) by group, actVB_mul,
          (GlobalTheory.PassPoly.mem_Dpcris_iff PC ρ _).1 hy _ hgs]
      refine ⟨?_, ?_⟩
      · rw [pow_succ', actVB_mul, ih.1, e1, ← actVB_mul, ← pow_succ']
      · rw [pow_succ', actVB_mul]
        exact GlobalTheory.PassPoly.Dpcris_stable PC ρ s _ hy
  rw [aeval_actVB PC.PD ρ g q (Nat.lt_succ_self _), aeval_actVB PC.PD ρ s q (Nat.lt_succ_self _)]
  exact Finset.sum_congr rfl fun n _ => by rw [(hpow n).1]

theorem prod_dvd_pow {R α β : Type} [CommRing R] [DecidableEq β] (M : Multiset α) (Sig : Finset β)
    (f : α → R) (v : β → R) (h : ∀ y ∈ M, ∃ a ∈ Sig, f y = v a) :
    (M.map fun y => X - C (f y)).prod ∣ (∏ a ∈ Sig, (X - C (v a))) ^ Multiset.card M := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons y M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    obtain ⟨a, ha, hya⟩ := h y (Multiset.mem_cons_self y M)
    refine mul_dvd_mul ?_ (ih fun z hz => h z (Multiset.mem_cons_of_mem hz))
    rw [hya]
    exact Finset.dvd_prod_of_mem (fun a => X - C (v a)) ha

set_option maxHeartbeats 4000000 in
open Classical in

theorem main : ∀ (D : D7) (P : Pend D), TieInePoly D → InertEq D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))), (∀ y ∈ Y, y ≠ 0 ∧ y ^ D.what₂.restRowsFiniteGroupCard = 1) →
  ∀ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c'),
  (∀ y ∈ Y, ∀ g ∈ GKin h,
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
        P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1) →
  ∃ ch : Fb (D.host.g k) (D.host.g_prime k) → ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ),
    ∀ S : Finset (Fb (D.host.g k) (D.host.g_prime k)), S ⊆ Y → ∀ (m : ℕ) (R : GE D.nd →* GL (Fin m) (D.nd.O i)),
      Continuous (fun g => ((R g : GL (Fin m) (D.nd.O i)) : Matrix (Fin m) (Fin m) (D.nd.O i))) →
      (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (R.comp (decS D.nd w))) →
      ∀ M : Multiset (Fb (D.host.g k) (D.host.g_prime k)), (∀ y ∈ M, y ∈ S) →
      (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) R) w) σ =
          (M.map fun y => X - C (P.om k w y σ)).prod) →
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep (R.comp (decS D.nd w))) (S.image ch) := by
  intro D P hTie hIE i k hik w hw Y hY K' h hN hF hS hH
  have hn : 0 < D.what₂.restRowsFiniteGroupCard := D.what₂.restRowsFiniteGroupCard_pos
  haveI : NeZero D.what₂.restRowsFiniteGroupCard := ⟨hn.ne'⟩
  have hιinj : Function.Injective (iotaO D.nd D.naut i) :=
    (((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  obtain ⟨ζ, hζ⟩ := P.zetaPrimitiveRoot i

  let ιg : ↥(GK (D.nbr i w hw).Kw) →* GE D.nd := (decS D.nd w).comp (D.nbr i w hw).e.symm.toMonoidHom
  have hιg : ∀ s, ιg s = (((D.nbr i w hw).e.symm s : Gw D.nd w) : GE D.nd) := fun s => rfl
  have hIne : ∀ s ∈ IK (D.nbr i w hw).Kw, ιg s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := by
    intro s hs
    rw [← hIE i w hw] at hs
    exact hs
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.exists_rootsOfUnity_character_hom (Γ := ↥(IK (D.nbr i w hw).Kw)) (F := Fb (D.host.g k) (D.host.g_prime k))
    (LL := ↥(D.nbr i w hw).LL.1) D.what₂.restRowsFiniteGroupCard hn (fun x s => P.om k w x (ιg s))
    (fun x hx => by simpa using P.om_one k w x hx)
    (fun x hx s s' => by
      simpa using P.om_mul k w x hx _ (hIne s s.2) _ (hIne s' s'.2))
    (fun x y hx hy s => P.tameInertiaChar_mul_root k w x y hx hy _ (hIne s s.2))
    (iotaO D.nd D.naut i) hιinj ζ hζ (D.nbr i w hw).toLL

  have hdec : ∀ g ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Iner, ∃ s ∈ IK (D.nbr i w hw).Kw, s⁻¹ * g ∈ GKin h :=
    fun g hg => GlobalTheory.InertiaDecomp.iner_decomp _ (D.loc (D.nd.l i)) _ K' h hN hF hS g hg
  have hYu : ∀ y ∈ (Y : Set (Fb (D.host.g k) (D.host.g_prime k))),
      ∃ u : ↥(rootsOfUnity D.what₂.restRowsFiniteGroupCard (Fb (D.host.g k) (D.host.g_prime k))),
        ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) = y := by
    intro y hy
    obtain ⟨hy0, hyn⟩ := hY y hy
    refine ⟨⟨Units.mk0 y hy0, ?_⟩, rfl⟩
    rw [mem_rootsOfUnity]; exact Units.ext (by simpa using hyn)
  have hYH : ∀ u : ↥(rootsOfUnity D.what₂.restRowsFiniteGroupCard (Fb (D.host.g k) (D.host.g_prime k))),
      ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) ∈
        (Y : Set (Fb (D.host.g k) (D.host.g_prime k))) →
      ∀ s : ↥(IK (D.nbr i w hw).Kw), (s : ↥(GK (D.nbr i w hw).Kw)) ∈ GKin h → Ψ u s = 1 := by
    intro u hu s hs
    obtain ⟨o, ho, ho'⟩ := hΨ u s
    have h1 : P.om k w ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) (ιg s) = 1 :=
      hH _ hu s hs (hIne s s.2)
    have h2 : o = 1 := hιinj (by rw [ho, map_one]; exact h1)
    exact Units.ext (by rw [ho', h2, map_one]; rfl)
  have X8 := GlobalTheory.extend_characters_and_generator (G := ↥(GK (D.nbr i w hw).Kw)) (F := Fb (D.host.g k) (D.host.g_prime k)) (LL := ↥(D.nbr i w hw).LL.1) (pc (D.loc (D.nd.l i)) h hN hF hS).Iner (IK (D.nbr i w hw).Kw) (GKin h) hN (IK_le_iner _ (D.loc (D.nd.l i)) _ K' h hN hF hS) hdec D.what₂.restRowsFiniteGroupCard hn Ψ (Y : Set (Fb (D.host.g k) (D.host.g_prime k))) hYu hYH
  obtain ⟨ch, hch, c, hc, hck⟩ := X8
  refine ⟨ch, fun S hSY m R hcont hpot M hMS hPol => ?_⟩
  have hSu : ∀ y ∈ S, ∃ u : ↥(rootsOfUnity D.what₂.restRowsFiniteGroupCard (Fb (D.host.g k) (D.host.g_prime k))),
      ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) = y ∧
      ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) ∈
        (Y : Set (Fb (D.host.g k) (D.host.g_prime k))) := by
    intro y hy
    obtain ⟨u, hu⟩ := hYu y (hSY hy)
    exact ⟨u, hu, hu ▸ hSY hy⟩

  have G1 : ∀ a ∈ S.image ch, ∀ g : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner,
      (g : ↥(GK (D.nbr i w hw).Kw)) ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).H → a g = 1 := by
    intro a ha g hg
    refine Exists.elim (Finset.mem_image.1 ha) fun y hy => ?_
    refine Exists.elim (hSu y hy.1) fun u hu => ?_
    rw [← hy.2, ← hu.1, hch u hu.2 g 1 (IK (D.nbr i w hw).Kw).one_mem (by rw [inv_one, one_mul]; exact hg)]
    exact map_one (Ψ u)
  have G2 : ∀ a ∈ S.image ch, Nat.Coprime (orderOf a) (D.nd.l i) := by
    intro a ha
    refine Exists.elim (Finset.mem_image.1 ha) fun y hy => ?_
    refine Exists.elim (hSu y hy.1) fun u hu => ?_
    have hu1 : u ^ orderOf (u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_orderOf_eq_one]; rfl)
    have hpow : a ^ orderOf (u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) = 1 := by
      ext g
      refine Exists.elim (hdec g g.2) fun s hs => ?_
      rw [MonoidHom.pow_apply, ← hy.2, ← hu.1, hch u hu.2 g s hs.1 hs.2, ← MonoidHom.pow_apply, ← map_pow, hu1,
        map_one]
      rfl
    have hchar : CharP (Fb (D.host.g k) (D.host.g_prime k)) (D.host.g k) := by
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      infer_instance
    have hcop := @coprime_orderOf (D.host.g k) ⟨D.host.g_prime k⟩ _ _ hchar
      (u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) D.what₂.restRowsFiniteGroupCard hn ((mem_rootsOfUnity _ _).1 u.2)
    have hc2 := Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hpow) hcop
    rwa [← hik] at hc2

  have G4 := exists_gen (G := ↥(GK (D.nbr i w hw).Kw)) (F := ↥(D.nbr i w hw).LL.1) (pc (D.loc (D.nd.l i)) h hN hF hS).Iner c D.what₂.restRowsFiniteGroupCard hn hc (S.image ch) (fun a ha => by
    refine Exists.elim (Finset.mem_image.1 ha) fun y hy => ?_
    rw [← hy.2]
    exact hck y (hSY hy.1))
  have G3 : ∀ g : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner, ∃ m' : ℕ,
      ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (R.comp (decS D.nd w))),
        (aeval (actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (R.comp (decS D.nd w)))
          (g : ↥(GK (D.nbr i w hw).Kw)))
          ((∏ a ∈ S.image ch, (X - C ((a g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1))) ^ m')) d = 0 := by
    intro g
    refine ⟨Multiset.card M, fun d hd => ?_⟩
    refine Exists.elim (hdec g g.2) fun s hs => ?_
    have hσ := hIne s hs.1
    have hO : ∀ y ∈ M, ∃ o : D.nd.O i, iotaO D.nd D.naut i o = P.om k w y (ιg s) ∧
        ((ch y g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1) = (D.nbr i w hw).toLL o := by
      intro y hy
      refine Exists.elim (hSu y (hMS y hy)) fun u hu => ?_
      refine Exists.elim (hΨ u ⟨s, hs.1⟩) fun o ho => ?_
      refine ⟨o, by rw [ho.1, hu.1], ?_⟩
      rw [← hu.1, hch u hu.2 g s hs.1 hs.2, ho.2]
    choose! o ho using hO
    have hpmap : ((M.map fun y => X - C (o y)).prod).map (iotaO D.nd D.naut i) =
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) R) w) (ιg s) := by
      rw [hPol _ hσ, Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun y hy => ?_
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, (ho y hy).1]
    have hT := hTie i w hw K' h hN hF hS m R hcont hpot ((D.nbr i w hw).e.symm s) hσ _ hpmap d hd
    have hq : ((M.map fun y => X - C (o y)).prod).map (D.nbr i w hw).toLL =
        (M.map fun y => X - C ((ch y g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1)).prod := by
      rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun y hy => ?_
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, (ho y hy).2]
    have hkill : (aeval (actVB (pc (D.loc (D.nd.l i)) h hN hF hS).PD ((D.nbr i w hw).rep (R.comp (decS D.nd w))) s)
        (((M.map fun y => X - C (o y)).prod).map (D.nbr i w hw).toLL)) d = 0 := by
      rw [aeval_actVB _ _ s _ (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self _))]
      refine Eq.trans (Finset.sum_congr rfl fun n _ => ?_) hT
      rw [Polynomial.coeff_map, map_pow, MulEquiv.apply_symm_apply]
      try rfl
    obtain ⟨r, hr⟩ := prod_dvd_pow M (S.image ch) (fun y => ((ch y g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1))
      (fun a => ((a g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1))
      (fun y hy => ⟨ch y, Finset.mem_image_of_mem ch (hMS y hy), rfl⟩)
    refine (aeval_eq_of_mem_Dpcris (pc (D.loc (D.nd.l i)) h hN hF hS) _ _ s hs.2 _ d hd).trans ?_
    rw [hr, mul_comm, map_mul, Module.End.mul_apply, ← hq, hkill, map_zero]
  exact GlobalTheory.PassPolyPow.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _ _
    (S.image ch) G1 G2 G3 G4
end GlobalTheory.InertiaChars
