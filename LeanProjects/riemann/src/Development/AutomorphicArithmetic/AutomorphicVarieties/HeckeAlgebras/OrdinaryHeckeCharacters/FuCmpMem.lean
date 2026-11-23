import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem fu_patch {G ι : Type} [Group G] [Finite ι] {H : ι → Type} [∀ i, Group (H i)] (p : ∀ i, G →* H i)
    (P : Subgroup G) (b : ∀ i, H i) (h : ∀ i, ∃ y ∈ P, p i y = b i ∧ ∀ j, j ≠ i → p j y = 1) :
    ∃ y ∈ P, ∀ i, p i y = b i := by
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ T : Finset ι, ∃ y ∈ P, (∀ i ∈ T, p i y = b i) ∧ ∀ i ∉ T, p i y = 1 := fun T => by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simp, fun i _ => map_one _⟩
    | insert a T ha ih =>
      obtain ⟨y, hy, h1, h2⟩ := ih
      obtain ⟨z, hz, h3, h4⟩ := h a
      refine ⟨y * z, mul_mem hy hz, fun i hi => ?_, fun i hi => ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · rw [map_mul, h2 _ ha, h3, one_mul]
        · rw [map_mul, h1 i hi, h4 i (fun e => ha (e ▸ hi)), mul_one]
      · rw [Finset.mem_insert, not_or] at hi
        rw [map_mul, h2 i hi.2, h4 i hi.1, mul_one]
  obtain ⟨y, hy, h1, -⟩ := key Finset.univ
  exact ⟨y, hy, fun i => h1 i (Finset.mem_univ i)⟩

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ}

private theorem fu_under (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [← s.hA v x, IsScalarTower.algebraMap_apply (Lp L) L Ω]
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm

omit [Fact l.Prime] [IsCMField L] in
private theorem fu_l (w : Plc L) : ((l : ℕ) : 𝓞 (Lp L)) ∈ (w.under (𝓞 (Lp L))).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L)) l]
  rfl

open scoped Pointwise in
private theorem fu_split (V : s.Lev) (w : Plc L) (hw : w.under (𝓞 (Lp L)) ∈ V.S') : IsSplitAt w := by
  by_contra hn
  have uq : ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → u = w := fun u hu => by
    by_contra h
    exact hn ⟨u, h, hu⟩
  have hA := s.hw (w.under (𝓞 (Lp L)))
  rw [uq _ (fu_under s _)] at hA
  have hD := V.split _ hw
  generalize s.A (w.under (𝓞 (Lp L))) = A at hA hD
  let τ : L ≃ₐ[Lp L] L := s.c.restrictNormal L
  have hl : IsLift τ.toRingEquiv s.c.toRingEquiv := fun x => (AlgEquiv.restrictNormal_commutes s.c L x).symm
  have h1 : IsPlaceOver (s.c⁻¹ • A) (preplace τ.toRingEquiv w) :=
    isPlaceOver_preplace hl (fun x => (ValuationSubring.mem_inv_pointwise_smul_iff (g := s.c) (S := A) (x := x)).symm) hA
  rw [uq (preplace τ.toRingEquiv w) (HeightOneSpectrum.ext (Ideal.ext fun x => by
    change RingOfIntegers.mapRingEquiv τ.toRingEquiv (algebraMap _ (𝓞 L) x) ∈ w.asIdeal ↔ algebraMap _ (𝓞 L) x ∈ w.asIdeal
    rw [show RingOfIntegers.mapRingEquiv τ.toRingEquiv (algebraMap _ (𝓞 L) x) = algebraMap _ (𝓞 L) x from
      Subtype.ext (τ.commutes x)]))] at h1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := L) hA h1
  have h2 : s.c * W.resP L Ω g ∈ Dec (F := Lp L) A := by
    refine mem_Dec.2 ?_
    have h3 : W.resP L Ω g • A = s.c⁻¹ • A := hg
    rw [mul_smul, h3, smul_inv_smul]
  have h4 : s.c ∈ (W.resP L Ω).range := (mul_mem_cancel_right (MonoidHom.mem_range.2 ⟨g, rfl⟩)).1 (hD h2)
  have h5 := (V.hη _).2 h4
  rw [V.η_c] at h5
  exact absurd h5 (by decide)

private theorem fu_cmp {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (g : UA L n) :
    cmp n w ((away l L n).rangeRestrict g) = cLoc w g := by
  rw [CaseU.cmp, dif_pos h]
  rfl

private theorem fu_cmp_mem (w : Plc L) (g : UA L n) {P : Subgroup (GLw n w)} (hg : cLoc w g ∈ P) :
    cmp n w ((away l L n).rangeRestrict g) ∈ P := by
  by_cases h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal
  · rw [CaseU.cmp, dif_neg (not_not.2 h)]
    exact one_mem _
  · rwa [fu_cmp h]

private theorem fu_open : IsOpen ((⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w) : Subgroup (UA L n)) : Set (UA L n)) := by
  let p : UA L n →* GL (Fin n) (Af L) := (Matrix.GeneralLinearGroup.map (pFin L)).comp (UA L n).subtype
  have hp : Continuous p := GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val
  have ho : IsOpen (GlobalTheory.GLIntegral.intSubring L : Set (Af L)) := RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 L) => (v.adicCompletionIntegers L : Set (v.adicCompletion L)))
    (fun v => Valued.isOpen_valuationSubring _)
  refine Subgroup.isOpen_mono (H₁ := (GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring L)).comap p) (fun g hg => ?_)
    ((GlobalTheory.GLIntegral.isOpen_glSub _ ho).preimage hp)
  have hv : ∀ (w : Plc L) (x : w.adicCompletion L), x ∈ w.adicCompletionIntegers L → x ∈ 𝒪[w.adicCompletion L] := fun w x hx => by
    haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
    exact hx
  exact Subgroup.mem_iInf.2 fun w => (GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => hv w _ (hg.1 i j w), fun i j => hv w _ (hg.2 i j w)⟩

end

private theorem fu_Kc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    IsOpen (Kc k n 1 : Set (GL (Fin n) k)) := by
  have key : ∀ I : Ideal 𝒪[k], I = maximalIdeal 𝒪[k] → (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk I)).ker =
      (Matrix.GeneralLinearGroup.map (n := Fin n) (residue 𝒪[k])).ker := by
    rintro _ rfl
    rfl
  rw [Kc, key _ (pow_one _)]
  exact GlobalTheory.StepData.isOpen_KOne

private theorem fu_Iw {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] (S : V → Plc L) (b : GV n S)
    (hb : ∀ v, b v ∈ (glIwa ((S v).adicCompletion L) n).I1 0) : b ∈ (iwS n S).Iw 0 := by
  choose x hx t ht y hy e using fun v => (iwMem _ _ 0 _).2.1.1 (hb v)
  rw [show b = x * t * y from funext e]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left fun v _ => hx v))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right fun v _ => (glIwa _ n).Tc_le 0 (ht v))))
    (Subgroup.mem_sup_right fun v _ => hy v)

private theorem fu_iInf {G ι : Type} [Group G] [TopologicalSpace G] [Finite ι] (H : ι → Subgroup G)
    (h : ∀ i, IsOpen (H i : Set G)) : IsOpen ((⨅ i, H i : Subgroup G) : Set G) := by
  rw [Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite h

theorem UpperTheory.V.Hi.finU :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ K, (hset Q τ₀).X.FinLevel ((hset Q τ₀).lev K) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K
  classical
  let Φ : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  have hsurj : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    obtain ⟨g, rfl⟩ := (away l L n).rangeRestrict_surjective a
    obtain ⟨y, hy, h1⟩ := fu_patch (fun v : V.frame.Vl => cLoc (n := n) (s.w v.1)) (away l L n).ker
      (fun v => (cLoc (s.w v.1) g)⁻¹ * b v) fun v => by
        obtain ⟨j, hj, h2, -⟩ := (secU l L Ω s n hn (s.w v.1)
          (fu_split V _ (by rw [fu_under]; exact V.sub (Or.inl v.2)))).1
        have h3 : ∀ x, ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ v.1 → cLoc u (j x) = 1 := fun x u hu =>
          Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hj x)).2 u) (by rwa [fu_under])
        refine ⟨j _, funext fun u => h3 _ u.1 fun e => u.2 (fu_l u.1 |>.1 (e ▸ v.2)), h2 _, fun v' hv => h3 _ _ ?_⟩
        rw [fu_under]
        exact fun e => hv (Subtype.ext e)
    refine ⟨g * y, Prod.ext (Subtype.ext ?_) (funext fun v => ?_)⟩
    · change away l L n (g * y) = away l L n g
      rw [map_mul, MonoidHom.mem_ker.1 hy, mul_one]
    · change cLoc (s.w v.1) (g * y) = b v
      rw [map_mul, h1 v, mul_inv_cancel_left]
  have hinf : ∀ x ∈ infU L n, Φ x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 w.1)) (funext fun v => h1 _)
  let K0 : Subgroup (UA L n) := ((⨅ w : Plc L, (KO (w.adicCompletion L) (Fin n)).comap (cLoc w)) ⊓
    (Kc _ n 1).comap (cLoc (s.w s.v0))) ⊓ ((⨅ q : Q.Q, Subgroup.comap (cLoc (Q.wq q)) (K.1 q)) ⊓
    ⨅ v : V.frame.Vl, ((glIwa ((s.w v.1).adicCompletion L) n).I1 0).comap (cLoc (s.w v.1)))
  have ho : IsOpen (K0 : Set (UA L n)) := by
    refine (fu_open.inter ((fu_Kc n).preimage (GlobalTheory.DefU.Inert.continuous_cLoc _))).inter (IsOpen.inter ?_ ?_)
    · exact fu_iInf _ fun q => (K.2 q).1.preimage (GlobalTheory.DefU.Inert.continuous_cLoc _)
    · exact fu_iInf _ fun v => ((glBridge _ n ℂ 1).2.2.1 0).1.preimage (GlobalTheory.DefU.Inert.continuous_cLoc _)
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite L n (K0.comap (GlobalTheory.UnitaryBC.finU L n).subtype)
    (ho.preimage continuous_subtype_val)
  refine ⟨S.image Φ, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := hsurj g
  obtain ⟨γ, hγ, x, hx, z, hz, k, ⟨⟨hk1, hk2⟩, hk3, hk4⟩, rfl⟩ := hS g
  replace hk1 : ∀ w : Plc L, cLoc w k.1 ∈ KO (w.adicCompletion L) (Fin n) := Subgroup.mem_iInf.1 hk1
  replace hk3 : ∀ q : Q.Q, cLoc (Q.wq q) k.1 ∈ K.1 q := Subgroup.mem_iInf.1 hk3
  let u : Ub n s := ⟨(away l L n).rangeRestrict k.1, Subgroup.mem_iInf.2 fun w => fu_cmp_mem _ _ (hk1 _), fu_cmp_mem (s.w s.v0) k.1 (P := Kc _ n 1) hk2⟩
  refine ⟨⟨γ, hγ⟩, Φ x, Finset.mem_image_of_mem _ hx, u, ?_, (Φ k.1).2, fu_Iw _ _ (Subgroup.mem_iInf.1 hk4), ?_⟩
  · have hq : ∀ q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => Q.range ▸ Or.inr ⟨q, rfl⟩
    obtain ⟨y, ⟨hy1, hy2⟩, h1⟩ := fu_patch (fun q : Q.Q => (cmp n (Q.wq q)).comp (Ub n s).subtype)
      ((⨆ q : Q.Q, Subgroup.map (sec n s (Q.wq q)) (K.1 q)) ⊓
        ⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ V.S'), ((cmp n w).comp (Ub n s).subtype).ker)
      (fun q => cLoc (Q.wq q) k.1) fun q => by
        obtain ⟨-, h2, h3⟩ := (secU l L Ω s n hn (Q.wq q) (fu_split V _ (hq q))).2 (Q.notS q)
        have h4 := fun w => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (h3 (cLoc (Q.wq q) k.1)) w)
        exact ⟨sec n s (Q.wq q) _, ⟨Subgroup.mem_iSup_of_mem q ⟨_, hk3 q, rfl⟩, Subgroup.mem_iInf.2 fun w =>
          Subgroup.mem_iInf.2 fun hw => h4 w fun e => hw (e ▸ hq q)⟩, h2 _, fun q' hq' => h4 _ fun e => hq' (Q.inj e)⟩
    rw [← inv_mul_cancel_right u y]
    refine mul_mem (Subgroup.mem_sup_left ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => ?_,
      Subgroup.mem_iInf.2 fun q => ?_⟩) (Subgroup.mem_sup_right hy1)
    · rw [Subgroup.mem_comap, map_mul, map_inv,
        MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy2 w) hw), inv_one, mul_one]
      exact fu_cmp_mem _ _ (hk1 _)
    · rw [MonoidHom.mem_ker, map_mul, map_inv, h1 q, mul_inv_eq_one]
      exact fu_cmp (fun h => Q.notS q (Or.inl ((fu_l _).2 h))) _
  · rw [map_mul, map_mul, map_mul, hinf z hz, mul_one]
    rfl
