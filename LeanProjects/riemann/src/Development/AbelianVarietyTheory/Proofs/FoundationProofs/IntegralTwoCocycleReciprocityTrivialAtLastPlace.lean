import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

variable {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {n : ℕ} {S : Finset Pl}
  {ξ : G ℚ Ω → G ℚ Ω → Qbar l}

def zcl {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ} (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n)
    (hξ : Coc2 c n S ξ) (i : Ix c) : H2 (charRep μ) :=
  Submodule.Quotient.mk ⟨zc c n S ξ i, zc_mem hμ hξ i⟩

theorem res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ) (i : Ix c) :
    resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0 := by
  obtain ⟨u, hu, huO, hcu⟩ := hcob
  unfold zcl resH2
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    separated_dvr_second_cohomology_mem]
  refine ⟨fun g => crd c n i (u g), continuous_crd hu.domRestrict (fun g => huO _) n i, ?_⟩
  funext ⟨g, h⟩
  rw [d1_apply, restrictCocycles2_apply]
  change _ = zc c n S ξ i (((g : G ℚ Ω) : GS Ω (S : Set Pl)), ((h : G ℚ Ω) : GS Ω (S : Set Pl)))
  rw [zc_mk hξ, MonoidHom.coe_comp, Function.comp_apply, charRep_apply]
  have hμg : ((μ (locFam S Av v g) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l g : ℤ_[l]) :=
    congrArg Units.val (DFunLike.congr_fun hμ (g : G ℚ Ω))
  rw [hμg]
  have hc := (cg_iff (hξ.int g h) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g))).1
    (hcu g g.2 h h.2) i
  rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (huO h)) (huO _)) (huO g),
    crd_sub i (algebraMap_mul_mem _ (huO h)) (huO _), crd_algebraMap_mul i _ (huO h)] at hc
  rw [hc]; rfl

theorem cob_of_res_zcl_eq_zero {μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ}
    (hμ : μ.comp (toGS Ω _) = cycMod ℚ Ω l n) (hξ : Coc2 c n S ξ) (Av : S → ValuationSubring Ω) (v : S)
    (h0 : ∀ i, resH2 (charRep μ) (locFam S Av v) (continuous_locFam S Av v) (zcl hμ hξ i) = 0) :
    Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
  have hb : ∀ i, ∃ ci : Dec (F := ℚ) (Av v) → ZMod (l ^ n), Continuous ci ∧
      d1 ((charRep μ).comp (locFam S Av v)) ci =
        fun p => zc c n S ξ i (((p.1 : G ℚ Ω) : GS Ω (S : Set Pl)), ((p.2 : G ℚ Ω) : GS Ω (S : Set Pl))) := by
    intro i
    have := h0 i
    unfold zcl resH2 at this
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      separated_dvr_second_cohomology_mem] at this
    exact this
  choose ci hci hd using hb
  classical
  refine ⟨fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Set.domRestrict (Dec (F := ℚ) (Av v) : Set (G ℚ Ω))
        fun s => if hs : s ∈ Dec (F := ℚ) (Av v) then lft c n (fun i => ci i ⟨s, hs⟩) else 0) =
        fun g => lft c n (fun i => ci i g) := by
      funext g; exact dif_pos g.2
    rw [this]
    exact Continuous.comp (g := lft c n) (f := fun g i => ci i g) continuous_of_discreteTopology
      (continuous_pi fun i => hci i)
  · intro s
    dsimp only
    split_ifs
    · exact lft_mem _ _
    · exact c.O.zero_mem
  · intro s hs t ht
    dsimp only
    rw [dif_pos ht, dif_pos ((Dec (F := ℚ) (Av v)).mul_mem hs ht), dif_pos hs]
    have hm : ∀ a, lft c n a ∈ c.O := lft_mem n
    refine (cg_iff (hξ.int s t) (c.O.add_mem (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _))).2
      fun i => ?_
    rw [crd_add i (c.O.sub_mem (algebraMap_mul_mem _ (hm _)) (hm _)) (hm _),
      crd_sub i (algebraMap_mul_mem _ (hm _)) (hm _), crd_algebraMap_mul i _ (hm _), crd_lft, crd_lft, crd_lft]
    have e := congrFun (hd i) (⟨s, hs⟩, ⟨t, ht⟩)
    rw [zc_mk hξ, d1_apply, MonoidHom.coe_comp, Function.comp_apply, charRep_apply] at e
    have hμg : ((μ (locFam S Av v ⟨s, hs⟩) : ZMod (l ^ n))) = PadicInt.toZModPow n (cycZ ℚ Ω l s : ℤ_[l]) :=
      congrArg Units.val (DFunLike.congr_fun hμ s)
    rw [hμg] at e
    rw [← e]; rfl

end GlobalTheory.Ord2.Rec

namespace GlobalTheory.Ord2.Rec

open GlobalTheory.Published.PoitouTate

theorem reciprocity : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (S : Finset Pl) (ξ : G ℚ Ω → G ℚ Ω → Qbar l) (v₀ : Pl),
    l ≠ 2 → ContainsAbove S l → Coc2 c n S ξ → v₀ ∈ S →
    (∀ v ∈ S, v ≠ v₀ → ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧ Cob2 c n (Dec (F := ℚ) B) ξ) →
    ∀ B : ValuationSubring Ω, IsPlaceOver B v₀ → Cob2 c n (Dec (F := ℚ) B) ξ := by
  intro hL l _ Ω _ _ _ c n S ξ v₀ hl hS hξ hv₀ hloc B hB
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ => 0, continuousOn_const, fun _ => c.O.zero_mem, fun s _ t _ => ?_⟩
    unfold Cg
    simp only [mul_zero, sub_zero, add_zero, pow_zero, norm_one]
    exact norm_le_one_of_mem (hξ.int s t)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.Published.exists_primitiveRoot_pow ℚ Ω l n
  obtain ⟨inv, hinv, hPT⟩ := hL.pt ℚ Ω l n (Or.inl hl) hn ζ hζ
  classical
  let Av : S → ValuationSubring Ω := fun v =>
    if h : v.1 = v₀ then B else Classical.choose (hloc v.1 v.2 h)
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := by
    intro v
    by_cases h : v.1 = v₀
    · simp only [Av, dif_pos h]; rw [h]; exact hB
    · simp only [Av, dif_neg h]; exact (Classical.choose_spec (hloc v.1 v.2 h)).1
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (F := ℚ) (Ω := Ω) (r := n) hS
  have hNT := (hPT S hS Av hAv μ hμ (ZMod (l ^ n)) (charRep μ) (contAction_charRep hμ)).1
  have hres : ∀ i, resH2 (charRep μ) (locFam S Av ⟨v₀, hv₀⟩) (continuous_locFam S Av _)
      (zcl hμ hξ i) = 0 := by
    intro i
    have hsum := hNT.sum_eq_zero (zcl hμ hξ i)
    rw [Finset.sum_eq_single ⟨v₀, hv₀⟩] at hsum
    · have hinj : Function.Injective (invAt S Av μ hμ inv ⟨v₀, hv₀⟩) :=
        (hinv _ _ (hAv ⟨v₀, hv₀⟩)).1.1.comp (toMuLoc_bijective S Av μ hμ _).1
      exact hinj (by rw [hsum, map_zero])
    · intro v _ hv
      have hne : v.1 ≠ v₀ := fun h => hv (Subtype.ext h)
      have hcob : Cob2 c n (Dec (F := ℚ) (Av v)) ξ := by
        simp only [Av, dif_neg hne]; exact (Classical.choose_spec (hloc v.1 v.2 hne)).2
      rw [res_zcl_eq_zero hμ hξ Av v hcob i, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hcob := cob_of_res_zcl_eq_zero hμ hξ Av ⟨v₀, hv₀⟩ hres
  have hA : Av ⟨v₀, hv₀⟩ = B := dif_pos rfl
  rw [hA] at hcob
  exact hcob

end GlobalTheory.Ord2.Rec
