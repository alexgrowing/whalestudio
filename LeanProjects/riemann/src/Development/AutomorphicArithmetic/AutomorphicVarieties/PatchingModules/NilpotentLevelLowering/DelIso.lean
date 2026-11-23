import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwIwQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa.Lev

private theorem di_card (l : ℕ) [hl : Fact l.Prime] (G : Type) [CommGroup G] [Finite G] :
    Nat.card (G ⧸ ellC l G) = l ^ padicValNat l (Nat.card G) := by
  classical
  have hl' := hl.out
  have hQ : IsPGroup l (G ⧸ ellC l G) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, c, hc, hbc⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' l hl'.ne_one
      refine ⟨b, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show (orderOf (x ^ l ^ b)).Coprime l
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hl'.ne_zero) ⟨c, hbc⟩, hbc,
        Nat.mul_div_cancel_left _ (pow_pos hl'.pos _)]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl').2 hc)
  have hC : ¬ l ∣ Nat.card (ellC l G) := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' l hd
    have h1 : (orderOf (y : G)).Coprime l := y.2
    rw [Subgroup.orderOf_coe, hy] at h1
    exact hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hpos : Nat.card (ellC l G) ≠ 0 := Nat.card_pos.ne'
  rw [hk, Subgroup.card_eq_card_quotient_mul_card_subgroup (ellC l G), hk,
    padicValNat.mul (pow_ne_zero _ hl'.ne_zero) hpos, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hC, add_zero]

private theorem di_cyc (l : ℕ) [Fact l.Prime] (G : Type) [CommGroup G] [Finite G] (x : G)
    (hx : Subgroup.zpowers x ⊔ ellC l G = ⊤) (a : ℕ) (ha : a = padicValNat l (Nat.card G)) :
    ∃ e : Multiplicative (ZMod (l ^ a)) ≃* G ⧸ ellC l G, e (Multiplicative.ofAdd 1) = (x : G ⧸ ellC l G) := by
  classical
  have hl' := (Fact.out : l.Prime)
  haveI : NeZero (l ^ a) := ⟨pow_ne_zero _ hl'.ne_zero⟩
  have hcard : Nat.card (G ⧸ ellC l G) = l ^ a := by rw [ha]; exact di_card l G
  let ψ : ZMod (l ^ a) →+ Additive (G ⧸ ellC l G) :=
    ZMod.lift (l ^ a) ⟨zmultiplesHom _ (Additive.ofMul (x : G ⧸ ellC l G)), by
      rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, ← hcard, pow_card_eq_one', ofMul_one]⟩
  let Φ : Multiplicative (ZMod (l ^ a)) →* G ⧸ ellC l G := AddMonoidHom.toMultiplicativeLeft ψ
  have hΦ : ∀ m : ℤ, Φ (Multiplicative.ofAdd (m : ZMod (l ^ a))) = (x : G ⧸ ellC l G) ^ m := by
    intro m
    show Additive.toMul (ψ (m : ZMod (l ^ a))) = _
    rw [ZMod.lift_coe]
    show Additive.toMul (zmultiplesHom _ (Additive.ofMul (x : G ⧸ ellC l G)) m) = _
    rw [zmultiplesHom_apply, toMul_zsmul, toMul_ofMul]
  have hsurj : Function.Surjective Φ := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H g =>
      have hg : g ∈ Subgroup.zpowers x ⊔ ellC l G := hx ▸ Subgroup.mem_top g
      obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hg
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      refine ⟨Multiplicative.ofAdd (m : ZMod (l ^ a)), ?_⟩
      rw [hΦ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).2 hv, mul_one, QuotientGroup.mk_zpow]
  have hbij : Function.Bijective Φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hcard]
    show Nat.card (ZMod (l ^ a)) ≤ _
    rw [Nat.card_zmod]
  refine ⟨MulEquiv.ofBijective Φ hbij, ?_⟩
  have h1 := hΦ 1
  rw [Int.cast_one, zpow_one] at h1
  exact h1

private theorem di_pi {q n : ℕ} (G : Fin q → Type) [∀ j, Group (G j)] (H K : ∀ j, Subgroup (G j))
    (Z : Fin q → Type) [∀ j, Group (Z j)] (f : ∀ j, H j →* (Fin n → Z j)) (hs : ∀ j, Function.Surjective (f j))
    (hk : ∀ j (g : H j), f j g = 1 ↔ (g : G j) ∈ K j)
    [((Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H)).Normal] :
    ∃ e : (∀ p : Fin q × Fin n, Z p.1) ≃*
        (Subgroup.pi Set.univ H ⧸ (Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H)),
      ∀ j i (z : Z j) (t : H j), f j t = Pi.mulSingle i z → ∃ g : Subgroup.pi Set.univ H,
        (g : ∀ j, G j) = Pi.mulSingle j (t : G j) ∧ e (Pi.mulSingle (j, i) z) = g := by
  classical
  let Φ : Subgroup.pi Set.univ H →* (∀ p : Fin q × Fin n, Z p.1) :=
    Pi.monoidHom fun p => (Pi.evalMonoidHom _ p.2).comp ((f p.1).comp
      (((Pi.evalMonoidHom G p.1).comp (Subgroup.pi Set.univ H).subtype).codRestrict (H p.1)
        fun g => (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)))
  have hΦ : ∀ (g : Subgroup.pi Set.univ H) (p : Fin q × Fin n),
      Φ g p = f p.1 ⟨(g : ∀ j, G j) p.1, (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)⟩ p.2 := fun g p => rfl
  have hsurj : Function.Surjective Φ := by
    intro z
    choose t ht using fun j => hs j (fun i => z (j, i))
    refine ⟨⟨fun j => (t j : G j), (Subgroup.mem_pi _).2 fun j _ => (t j).2⟩, funext fun p => ?_⟩
    rw [hΦ]
    exact congrFun (ht p.1) p.2
  have hker : Φ.ker = (Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_pi]
    constructor
    · intro h j _
      refine (hk j ⟨_, (Subgroup.mem_pi _).1 g.2 j (Set.mem_univ _)⟩).1 (funext fun i => ?_)
      have := congrFun h (j, i)
      rw [hΦ] at this
      exact this
    · intro h
      funext p
      rw [hΦ]
      exact congrFun ((hk p.1 ⟨_, (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)⟩).2 (h p.1 (Set.mem_univ _))) p.2
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective Φ hsurj).symm.trans (QuotientGroup.quotientMulEquivOfEq hker), ?_⟩
  intro j i z t ht
  have hmemg : Pi.mulSingle j (t : G j) ∈ Subgroup.pi Set.univ H := by
    refine (Subgroup.mem_pi _).2 fun j' _ => ?_
    by_cases h : j' = j
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact t.2
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  have hΦg : Φ ⟨_, hmemg⟩ = Pi.mulSingle (j, i) z := by
    funext p
    obtain ⟨j', i'⟩ := p
    rw [hΦ]
    by_cases h : j' = j
    · subst h
      have key : f j' ⟨Pi.mulSingle j' (t : G j') j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ = f j' t := by
        congr 1
        exact Subtype.ext (Pi.mulSingle_eq_same _ _)
      rw [key, ht]
      by_cases hi : i' = i
      · subst hi
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne (fun hp => hi (congrArg Prod.snd hp))]
    · have key : f j' ⟨Pi.mulSingle j (t : G j) j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ = 1 := by
        rw [show (⟨Pi.mulSingle j (t : G j) j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ : H j') = 1 from
          Subtype.ext (Pi.mulSingle_eq_of_ne h _), map_one]
      rw [key, Pi.mulSingle_eq_of_ne (fun hp => h (congrArg Prod.fst hp))]
      rfl
  refine ⟨⟨_, hmemg⟩, rfl, ?_⟩
  have hs1 : (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj).symm (Φ ⟨_, hmemg⟩) =
      ((⟨_, hmemg⟩ : Subgroup.pi Set.univ H) : Subgroup.pi Set.univ H ⧸ Φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, ← hΦg, hs1, QuotientGroup.quotientMulEquivOfEq_mk]

private theorem di_loc (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n l : ℕ)
    [Fact l.Prime] (δ : kˣ) (hδ : IsGenMod k (ellC l _) δ) :
    ∃ f : iwC k n ⊤ →* (Fin n → Multiplicative (ZMod (l ^ padicValNat l (resCard k - 1)))), Function.Surjective f ∧
      (∀ g : iwC k n ⊤, f g = 1 ↔ (g : GL (Fin n) k) ∈ iwC k n (ellC l _)) ∧
      ∀ i, ∃ t : iwC k n ⊤, (t : GL (Fin n) k) = diagT k (Fin n) (Pi.mulSingle i δ) ∧
        f t = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
  classical
  obtain ⟨d, hdδ, hgen⟩ := hδ
  obtain ⟨f0, hs0, hk0, hv0⟩ := iwQuot k n (ellC l 𝓀[k]ˣ)
  obtain ⟨e, he⟩ := di_cyc l _ _ hgen (padicValNat l (resCard k - 1)) (by rw [Nat.card_units]; rfl)
  refine ⟨(MonoidHom.compLeft e.symm.toMonoidHom (Fin n)).comp f0, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨g, hg⟩ := hs0 (fun i => e (y i))
    refine ⟨g, funext fun i => ?_⟩
    show e.symm (f0 g i) = y i
    rw [hg]
    exact e.symm_apply_apply (y i)
  · intro g
    rw [← hk0 g]
    constructor
    · intro h
      funext i
      exact (MulEquiv.map_eq_one_iff e.symm).1 (congrFun h i)
    · intro h
      funext i
      show e.symm (f0 g i) = 1
      rw [congrFun h i]
      exact map_one e.symm
  · intro i
    let u : Fin n → 𝒪[k]ˣ := Pi.mulSingle i d
    have hmem : ∀ w : Fin n → 𝒪[k]ˣ,
        diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) (w i)) ∈ iwC k n ⊤ := by
      intro w
      unfold iwC
      refine Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ ?_)
      unfold torC unitsC
      exact (Subgroup.mem_pi _).2 fun i' _ => Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 (Subgroup.mem_top _))
    refine ⟨⟨_, hmem u⟩, ?_, ?_⟩
    · show diagT k (Fin n) _ = _
      congr 1
      funext i'
      by_cases h : i' = i
      · rw [h]
        simp only [u, Pi.mulSingle_eq_same]
        exact hdδ
      · simp only [u, Pi.mulSingle_eq_of_ne h, map_one]
    · funext i'
      refine (congrArg e.symm (hv0 u (hmem u) i')).trans ?_
      by_cases h : i' = i
      · rw [h]
        simp only [u, Pi.mulSingle_eq_same]
        rw [MulEquiv.symm_apply_eq]
        exact he.symm
      · simp only [u, Pi.mulSingle_eq_of_ne h, map_one, QuotientGroup.mk_one]

end UpperTheory.V.Pa.Lev

theorem UpperTheory.V.Pa.Lev.delIso :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) [Fact l.Prime] (δ : ∀ j, ((w j).adicCompletion L)ˣ) [((UIw1 l n w).subgroupOf (UIw n w)).Normal], (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∃ e : Del l n (fun j => padicValNat l (qj w j - 1)) ≃* (UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)), ∀ j i, ∃ g : UIw n w, (g : GV n w) = atJ n w j (diagT _ (Fin n) (Pi.mulSingle i (δ j))) ∧ e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1)) = (g : UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)) := by
  intro L _ _ n q w l _ δ _ hδ
  choose f hs hk ht using fun j => di_loc ((w j).adicCompletion L) n l (δ j) (hδ j)
  haveI hN : ((Subgroup.pi Set.univ (fun j => iwC ((w j).adicCompletion L) n (ellC l _))).subgroupOf
      (Subgroup.pi Set.univ (fun j => iwC ((w j).adicCompletion L) n ⊤))).Normal :=
    (inferInstance : ((UIw1 l n w).subgroupOf (UIw n w)).Normal)
  obtain ⟨e, he⟩ := di_pi (fun j => GLw n (w j)) (fun j => iwC ((w j).adicCompletion L) n ⊤)
    (fun j => iwC ((w j).adicCompletion L) n (ellC l _))
    (fun j => Multiplicative (ZMod (l ^ padicValNat l (qj w j - 1)))) f hs hk
  refine ⟨e, fun j i => ?_⟩
  obtain ⟨t, htd, htf⟩ := ht j i
  obtain ⟨g, hg, heg⟩ := he j i _ t htf
  refine ⟨g, ?_, heg⟩
  show (g : ∀ j, GLw n (w j)) = _
  rw [hg, htd]
  rfl
