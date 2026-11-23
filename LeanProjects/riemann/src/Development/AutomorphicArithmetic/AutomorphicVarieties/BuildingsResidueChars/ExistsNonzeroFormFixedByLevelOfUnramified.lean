import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedVectorOfLocalFixedVectors
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnderChosenPlaceAndIsSplitAtOfDecompLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem locU_congr {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w u : Plc L}
    (h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) {x : UA L n} (hx : x ∈ locU n w) : x ∈ locU n u := by
  unfold locU at hx ⊢
  rw [h]
  exact hx

private theorem local_retraction_component_cases {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (w u : Plc L) (x : UA L n) :
    cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = cLoc u x ∨ cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = 1 := by
  by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
  · exact Or.inl (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq h x)
  · exact Or.inr (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne h x)

private theorem local_retraction_mem_comap {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (w u : Plc L) (x : UA L n)
    {H : Subgroup (GL (Fin n) (u.adicCompletion L))} (hx : cLoc u x ∈ H) : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) ∈ H := by
  rcases local_retraction_component_cases w u x with h | h <;> rw [h]
  · exact hx
  · exact one_mem _

private theorem local_retraction_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (w u : Plc L) (x : UA L n)
    (hx : cLoc u x = 1) : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = 1 :=
  (local_retraction_component_cases w u x).elim (fun h => h.trans hx) id

private theorem ne_zero_of_irr {G H W M : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup M] [Module ℂ M]
    (p : G →* H) (hp : Function.Surjective p) (ρ : Representation ℂ H W) (hρ : ρ.IsIrreducible) (R : G → M →ₗ[ℂ] M)
    (f : W →ₗ[ℂ] M) (hf : f ≠ 0) (he : ∀ x v, f (ρ (p x) v) = R x (f v)) {v : W} (hv : v ≠ 0) : f v ≠ 0 := by
  intro h0
  let S : Subrepresentation ρ := ⟨LinearMap.ker f, fun g y hy => by
    obtain ⟨x, rfl⟩ := hp g
    rw [LinearMap.mem_ker] at hy ⊢
    rw [he, hy, map_zero]⟩
  rcases hρ.eq_bot_or_eq_top S with h | h
  · have h1 : LinearMap.ker f = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hv (by simpa [h1] using (LinearMap.mem_ker.2 h0))
  · have h1 : LinearMap.ker f = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact hf (LinearMap.ker_eq_top.1 h1)

theorem UpperTheory.exists_nonzero_form_fixed_by_level_of_unramified :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (σ : Submodule ℂ (UA L n → ℂ)), IsAutRepU σ → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) → (∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧ fixd τ.ρ (Kc _ n 1) ≠ ⊥) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ GlobalTheory.UnitaryBC.finU L n, (∀ u : Plc L, u.under (𝓞 (Lp L)) ∉ V.S' → cLoc u k ∈ KO (u.adicCompletion L) (Fin n)) → cLoc (s.w s.v0) k ∈ Kc _ n 1 → (∀ v : V.frame.Vl, cLoc (s.w v.1) k = 1) → (∀ u : s.St, cLoc (s.w u) k = 1) → (∀ q : Q.Q, cLoc (Q.wq q) k = 1) → RU L n k φ = φ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q σ hσ hun hτ
  obtain ⟨hund, hspl⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  have hsplit : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ V.S' → IsSplitAt w := fun w hw => hspl w (V.split _ hw)
  let K : Subgroup (UA L n) :=
    { carrier := {k | k ∈ GlobalTheory.UnitaryBC.finU L n ∧
        (∀ u : Plc L, u.under (𝓞 (Lp L)) ∉ V.S' → cLoc u k ∈ KO (u.adicCompletion L) (Fin n)) ∧
        cLoc (s.w s.v0) k ∈ Kc _ n 1 ∧ (∀ v : V.frame.Vl, cLoc (s.w v.1) k = 1) ∧ (∀ u : s.St, cLoc (s.w u) k = 1) ∧
        (∀ q : Q.Q, cLoc (Q.wq q) k = 1)}
      one_mem' := ⟨one_mem _, fun u _ => by rw [map_one]; exact one_mem _, by rw [map_one]; exact one_mem _,
        fun _ => map_one _, fun _ => map_one _, fun _ => map_one _⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1,
        fun u hu => by rw [map_mul]; exact mul_mem (ha.2.1 u hu) (hb.2.1 u hu),
        by rw [map_mul]; exact mul_mem ha.2.2.1 hb.2.2.1,
        fun v => by rw [map_mul, ha.2.2.2.1 v, hb.2.2.2.1 v, one_mul],
        fun v => by rw [map_mul, ha.2.2.2.2.1 v, hb.2.2.2.2.1 v, one_mul],
        fun v => by rw [map_mul, ha.2.2.2.2.2 v, hb.2.2.2.2.2 v, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1,
        fun u hu => by rw [map_inv]; exact inv_mem (ha.2.1 u hu),
        by rw [map_inv]; exact inv_mem ha.2.2.1,
        fun v => by rw [map_inv, ha.2.2.2.1 v, inv_one],
        fun v => by rw [map_inv, ha.2.2.2.2.1 v, inv_one],
        fun v => by rw [map_inv, ha.2.2.2.2.2 v, inv_one]⟩ }
  have hKO : ∀ u : Plc L, KO (u.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL u n :=
    fun u => GlobalTheory.SmGL.SphCompletion.KO_completion u n
  have hT : ((fun w : Plc L => w.under (𝓞 (Lp L))) ⁻¹' V.S').Finite := by
    refine V.fin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
      (f := fun w : Plc L => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  have key := UpperTheory.exists_fixed_vector_of_local_fixed_vectors L n σ hσ K (fun k hk => hk.1)
    (fun w k hk => ⟨(Subgroup.mem_inf.1 (GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k)).1,
      fun u hu => local_retraction_mem_comap w u k (hk.2.1 u hu), local_retraction_mem_comap w _ k hk.2.2.1,
      fun v => local_retraction_eq_one w _ k (hk.2.2.2.1 v), fun v => local_retraction_eq_one w _ k (hk.2.2.2.2.1 v),
      fun v => local_retraction_eq_one w _ k (hk.2.2.2.2.2 v)⟩) _ hT
    (fun k hk u hu => hKO u ▸ hk.2.1 u hu) ?_
  · obtain ⟨φ, h1, h2, h3⟩ := key
    exact ⟨φ, h1, h2, fun k a b c d e f => h3 k ⟨a, b, c, d, e, f⟩⟩
  intro w
  have htriv : ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → w.under (𝓞 (Lp L)) ∈ V.S' →
      (∀ k ∈ K, cLoc u k = 1) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, k ∈ locU n w → RU L n k φ = φ := by
    intro u hu hw h1
    obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    refine ⟨φ, hφ, h0, fun k hk hl => ?_⟩
    have h2 : k = 1 := congrArg Subtype.val
      (GlobalTheory.SplitPts.eq_one_of_cLoc (hsplit u (hu ▸ hw)) ⟨k, locU_congr hu hl⟩ (h1 k hk))
    rw [h2, map_one]
    rfl
  by_cases hw : w.under (𝓞 (Lp L)) ∈ V.S'
  · have hw' := hw
    rw [Q.range] at hw'
    rcases hw' with (h | h | h) | ⟨q, h⟩
    · exact htriv (s.w _) (hund _) hw fun k hk => hk.2.2.2.1 ⟨_, h⟩
    · exact htriv (s.w _) (hund _) hw fun k hk => hk.2.2.2.2.1 ⟨_, h⟩
    · obtain ⟨τ, ⟨hirr, f, hf, hfσ, he⟩, hfix⟩ := hτ
      have hu : (s.w s.v0).under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := (hund _).trans h.symm
      obtain ⟨⟨j, hj1, hj2, -⟩, -⟩ := UpperTheory.V.Hi.secU l L Ω s n hn (s.w s.v0) (hsplit _ (hu ▸ hw))
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
      refine ⟨f v, hfσ v, ne_zero_of_irr _ (fun g => ⟨⟨j g, hj1 g⟩, hj2 g⟩) τ.ρ hirr
        (fun x => RU L n (x : locU n (s.w s.v0))) f hf he hv0, fun k hk hl => ?_⟩
      rw [← he ⟨k, locU_congr hu hl⟩ v]
      exact congrArg f (hv _ hk.2.2.1)
    · exact htriv (Q.wq q) h hw fun k hk => hk.2.2.2.2.2 q
  · obtain ⟨φ, h1, h2, h3⟩ := hun w hw
    exact ⟨φ, h1, h2, fun k hk hl => h3 k hl (hKO w ▸ hk.2.1 w hw)⟩
