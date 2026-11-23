import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.TypeValues

section General

variable {L : Type} [Field L] [NumberField L]

theorem productRule (χ : HChar L) : χ.ProductRule :=
  GlobalTheory.Mem.Chr.CharModel.productRule (F := L) ⟨χ.1, χ.2⟩

theorem inf_eq_one [IsTotallyComplex L] (χ : HChar L) {n : ℕ} (hn : 0 < n) (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hpow : ∀ x, χ.1 x ^ n = 1 := fun x => by
    have h1 : (χ ^ n).1 x = 1 := by rw [show χ ^ n = 1 from h]; rfl
    simpa using h1
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz0 : e.symm z ≠ 0 := by
    intro h0
    have h1 : z = 0 := by simpa using congrArg e h0
    rw [h1, zero_pow hn.ne'] at hz
    exact (atInf w k).ne_zero (e.injective (by rw [← hz, map_zero]))
  have hk : atInf w k = Units.mk0 _ hz0 ^ n := Units.ext (e.injective (by
    rw [← hz, Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, RingEquiv.apply_symm_apply]))
  rw [MonoidHom.comp_apply, hk, map_pow, map_pow, hpow]

theorem val_atFin (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = v.intValuation a := by
  have h : Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = v.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
  rw [h, hk]
  exact v.valuation_of_algebraMap a

theorem locK_eq_one {χ : HChar L} {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (k : Lˣ) (a : 𝓞 L) (hk : (k : L) = a)
    (ha : a - 1 ∈ v.asIdeal) : χ.locK v k = 1 := by
  refine h _ ?_ ?_
  · unfold IsUnitAt
    rw [val_atFin v k a hk]
    refine v.intValuation_eq_one_iff.2 fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    simpa using v.asIdeal.sub_mem h1 ha
  · have h1 : ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
        algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L (a - 1)) := by
      rw [map_sub, map_sub, map_one, map_one]
      congr 1
      show algebraMap L (v.adicCompletion L) (k : L) = _
      rw [hk]
    have h2 : Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L (a - 1))) =
        v.valuation L (algebraMap (𝓞 L) L (a - 1)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    rw [h1, h2, v.valuation_of_algebraMap, v.intValuation_le_pow_iff_mem, pow_one]
    exact ha

theorem exists_lift_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    {P : HeightOneSpectrum (𝓞 L)} (hP : P ∈ S) (u : (𝓞 L ⧸ P.asIdeal)ˣ) :
    ∃ (a : 𝓞 L) (k : Lˣ), (k : L) = a ∧ (u : 𝓞 L ⧸ P.asIdeal) = Ideal.Quotient.mk _ a ∧ χ.locK P k ∈ Λ := by
  classical
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ P.asIdeal)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have hua : (u : 𝓞 L ⧸ P.asIdeal) = Ideal.Quotient.mk _ a := by
    have h1 := ha P hP
    rw [if_pos rfl, pow_one] at h1
    rw [← hb]
    exact (Ideal.Quotient.eq.2 h1).symm
  have : Nontrivial (𝓞 L ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : L) ≠ 0 := by
    intro h0
    have h1 : a = 0 := by exact_mod_cast h0
    exact u.ne_zero (by rw [hua, h1, map_zero])
  refine ⟨a, Units.mk0 _ ha0, rfl, hua, ?_⟩
  have h := productRule χ S hu (Units.mk0 _ ha0)
  rw [hi, one_mul, Finset.prod_eq_single_of_mem P hP (fun v hvS hvP => locK_eq_one (ht v) _ a rfl (by
    have h1 := ha v hvS
    rwa [if_neg hvP, pow_one] at h1))] at h
  rw [eq_inv_of_mul_eq_one_left h]
  refine Λ.inv_mem (finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun v => ?_)
  exact finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun hvS => Λ.zpow_mem (hv v hvS) _

theorem intValuation_eq_of_mem {v : HeightOneSpectrum (𝓞 L)} {a : 𝓞 L} (h1 : a ∈ v.asIdeal) (h2 : a ∉ v.asIdeal ^ 2) :
    v.intValuation a = WithZero.exp (-1 : ℤ) := by
  have h0 : v.intValuation a ≠ 0 := v.intValuation_ne_zero a (by rintro rfl; exact h2 (zero_mem _))
  have h3 := (v.intValuation_le_pow_iff_mem a 1).2 (by rwa [pow_one])
  have h4 := mt (v.intValuation_le_pow_iff_mem a 2).1 h2
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp] at h3 h4
  rw [← WithZero.exp_log h0]
  congr 1
  push_cast at h3 h4
  omega

end General

section CM

open Formalism.L2.Col

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem exists_norm (hc : Formalism.BasicNotions.CMData F E) (a : 𝓞 E) :
    ∃ f : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) f = a * cO E a := by
  obtain ⟨f, hf⟩ := (hc.fixed ((a * cO E a : 𝓞 E) : E)).1 (by
    show star (algebraMap (𝓞 E) E (a * cO E a)) = algebraMap (𝓞 E) E (a * cO E a)
    rw [map_mul, algebraMap_cO, star_mul', star_star, mul_comm])
  have hi : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hf]
    exact (a * cO E a).2
  exact ⟨⟨f, hi⟩, RingOfIntegers.ext hf⟩

theorem val_sq_eq_one (hc : Formalism.BasicNotions.CMData F E) {χ : HChar E} (ht : χ.TrivOn F) {v : HeightOneSpectrum (𝓞 E)}
    (hu : χ.UnrAt v) (hv : conjPrime₂ v = v) : χ.val v ^ 2 = 1 := by
  have hmem : ∀ a, cO E a ∈ v.asIdeal ↔ a ∈ v.asIdeal := fun a => by rw [← mem_conjP, hv]
  have hab : aboveF (L := E) F (v.under (𝓞 F)) = {v} := by
    ext P
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_singleton]
    refine ⟨fun h => HeightOneSpectrum.ext (P.isMaximal.eq_of_le v.isPrime.ne_top fun a ha => ?_), fun h => by rw [h]; rfl⟩
    obtain ⟨f, hf⟩ := exists_norm hc a
    have h1 : f ∈ (P.under (𝓞 F)).asIdeal := by
      show algebraMap (𝓞 F) (𝓞 E) f ∈ P.asIdeal
      rw [hf]; exact P.asIdeal.mul_mem_right _ ha
    rw [show P.under (𝓞 F) = v.under (𝓞 F) from h] at h1
    have h2 : algebraMap (𝓞 F) (𝓞 E) f ∈ v.asIdeal := h1
    rw [hf] at h2
    exact (v.isPrime.mem_or_mem h2).elim id (hmem a).1
  obtain ⟨a, ha1, ha2⟩ : ∃ a ∈ v.asIdeal, a ∉ v.asIdeal ^ 2 := by
    have := Ideal.pow_succ_lt_pow v.ne_bot 1 (P := v.asIdeal)
    rw [pow_one] at this
    exact SetLike.exists_of_lt this
  have hb2 : cO E a ∉ v.asIdeal ^ 2 := fun h => ha2 (by
    have h1 := Ideal.mem_map_of_mem (cO E) h
    rw [cO_cO, Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => (hmem x).2 hx) 2 h1)
  have hne : ∀ x : 𝓞 E, x ∉ v.asIdeal ^ 2 → (x : E) ≠ 0 := fun x hx h0 => by
    have h1 : x = 0 := by exact_mod_cast h0
    exact hx (h1 ▸ zero_mem _)
  have hval : ∀ (x : 𝓞 E) (_ : x ∈ v.asIdeal) (h2 : x ∉ v.asIdeal ^ 2), χ.locK v (Units.mk0 _ (hne x h2)) = χ.val v :=
    fun x h1 h2 => χ.val_eq hu _ (by
      unfold IsUnifAt
      rw [val_atFin v _ x rfl, intValuation_eq_of_mem h1 h2])
  obtain ⟨f, hf⟩ := exists_norm hc a
  have hfE : algebraMap F E (f : F) = (a : E) * (cO E a : 𝓞 E) := by
    have := congrArg (algebraMap (𝓞 E) E) hf
    rw [map_mul] at this
    exact this
  have hf0 : (f : F) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hfE
    exact mul_ne_zero (hne a ha2) (hne _ hb2) hfE.symm
  have h := ht.1 (v.under (𝓞 F)) (Units.mk0 _ hf0)
  rw [HChar.resFin, hab, Finset.prod_singleton, MonoidHom.comp_apply,
    show upF F (Units.mk0 _ hf0) = Units.mk0 _ (hne a ha2) * Units.mk0 _ (hne _ hb2) from Units.ext hfE,
    map_mul, hval a ha1 ha2, hval _ ((hmem a).2 ha1) hb2] at h
  rw [sq, h]

end CM

end GlobalTheory.TypeValues

end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace GlobalTheory.RationalValues

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
  Formalism.L2.Host Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def unitsIn (M : Subfield ℂ) : Subgroup ℂˣ where
  carrier := {z | (z : ℂ) ∈ M}
  one_mem' := M.one_mem
  mul_mem' := fun h h' => M.mul_mem h h'
  inv_mem' := fun {z} h => by
    show ((z⁻¹ : ℂˣ) : ℂ) ∈ M
    rw [Units.val_inv_eq_inv_val]
    exact M.inv_mem h

theorem type_mem (i : Fin D.R.m) (t : T0) (M : Subfield ℂ)
    (hχ : ∀ PP ∈ R.Pg, ∀ x, ((R.chi ((i : ℕ) + 1) PP x : ℂˣ) : ℂ) ∈ M)
    (hξ : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t PP x : ℂˣ) : ℂ) ∈ M) (k : levJ R i t) :
    (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) ∈ M := by
  show levFn (R.βV i) (Lev.flag1L (R.datVt i t)) _ ∈ unitsIn M
  unfold levFn
  refine mul_mem (mul_mem ?_ (prod_mem fun PP hPP => prod_mem fun c _ => ?_)) (prod_mem fun PP hPP => hξ PP hPP _)
  · have h1 : ∀ x, ext1 (Lev.flag1L (R.datVt i t)).P.H (Lev.flag1L (R.datVt i t)).P.chi x = 1 := fun x => Lev.subgroupCharExtension_one_apply _ x
    rw [h1]
    exact one_mem _
  · exact inv_mem (show R.chi ((i : ℕ) + 1) PP _ ∈ unitsIn M from hχ PP hPP _)

theorem exists_isRatMat {V : HSp D} (γ : GQ V) : ∃ γE, Bridge.IsRatMat V γ γE := by
  obtain ⟨x, hx⟩ := γ
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
  exact ⟨y, hy.symm⟩

theorem smul_eq_of {K X W : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}
    (c : X →ₛₗ[σ] W) {a : K} {z : ℂ} {x : X} {w : W} (ha : σ a = z) (hx : c x = w) : z • w = c (a • x) := by
  rw [map_smulₛₗ, ha, hx]

theorem exists_ext_eq {Γ H W K X : Type} [Group H] [Group Γ] {ι : Γ →* H} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (c0 : X → W) (h₁ : ∀ x, ∃ v, P.coef x = c0 v) (h₂ : ∀ γ v, ∃ v', c0 v' = ρ γ (c0 v))
    (f : S.Forms) (g : H) : ∃ k v, P.extL f g = (χ k : ℂ) • c0 v := by
  obtain ⟨v, hv⟩ := h₁ (f.1 (P.decC g))
  obtain ⟨v', hv'⟩ := h₂ (P.decG g) v
  exact ⟨P.decK g, v', by rw [hv', ← hv]; rfl⟩

theorem coef_mem {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del} (h : Bridge.CoefTie V C P lam c0 pair nab del) (x : S.V) :
    ∃ v, P.coef x = c0 v := by
  obtain ⟨e, -, he, -⟩ := h
  exact ⟨e x, he x⟩

theorem rho_mem {V : HSp D} {C : Bridge.CoefDat D V} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {rho} (h : Bridge.CoefMapTie V C c0 rho) (γ : GQ V) (v : VV D.what₂.LL lam) :
    ∃ v', c0 v' = C.ρ γ (c0 v) := by
  obtain ⟨γE, hγ⟩ := exists_isRatMat γ
  exact ⟨_, h.1 γ γE hγ v⟩

set_option maxHeartbeats 1600000 in

theorem exists_jV_eq (i : Fin D.R.m) (t : T0) {gramR c0R c0L} (hj : R.models_jV)
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L)
    (x₀ : A.fam.amb.FL i t) (g : Bridge.Gf (Vc D i)) :
    ∃ (k : levJ R i t) (v : VsV D i D.what₂.LL), (R.HV i t).e (jVx R i t x₀) g =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) • (c0L i v : (R.cV i).W) := by
  have h0 := congrFun (hj i t x₀) g
  have h1 := coef_mem (hT.coefL i t)
  have h2 := rho_mem (hT.mapL i)
  have h3 := exists_ext_eq (R.B.L i t).pres (c0L i) h1 h2 x₀ g
  exact h3.imp fun k hk => hk.imp fun v hv => h0.trans hv

set_option maxHeartbeats 1600000 in

theorem placeEx_of_type_mem (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ) (t : T0)
    {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) {gramR c0R c0L}
    (hj : R.models_jV)
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L)
    (hc : CoefficientBaseChange R i jL σ' (c0L i) c0')
    (hk : ∀ k : levJ R i t, (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) ∈ σ'.fieldRange) :
    PlaceEx R i t h c0' := by
  intro x₀
  have key : ∀ g, ∃ y, (R.HV i t).e (jVx R i t x₀) g = c0' y := fun g => by
    have h0 := exists_jV_eq R i t hj hT x₀ g
    obtain ⟨k, v, hv⟩ := h0
    obtain ⟨a, ha⟩ := hk k
    obtain ⟨v', -, hv'⟩ := hc v
    exact ⟨a • v', hv.trans (smul_eq_of c0' ha hv')⟩
  choose y hy using key
  exact ⟨fun k => y (fin _ (h k)), fun k => hy _⟩

theorem chiVal_of_chiW (hW : R.grp_chiW) : ChiVal R := by
  classical
  intro i PP hPP x
  have : Nonempty (Fin D.R.r) := ⟨⟨0, by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r
    omega⟩⟩
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin D.R.r) x
  refine ⟨((R.FW i).chi (R.eG.symm (Pi.mulSingle (⟨PP, hPP⟩ : R.Pg) g)) : D.what₂.LLˣ), ?_⟩
  rw [hW, MulEquiv.apply_symm_apply, Finset.prod_eq_single (⟨PP, hPP⟩ : R.Pg), Pi.mulSingle_eq_same, hg]
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

theorem conjP_conjP (P : Pl D.host.E) : conjPrime₂ (conjPrime₂ P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun a => by rw [mem_conjP, mem_conjP, cO_cO])

theorem xiR_mem (hL : R.toLevCh.Is A.μ0) (hon : R.fam_pl_onto) (hmu : R.fam_muVal)
    (hok : ∀ t P, P ∈ A.ok t ↔ Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))))
    (i : Fin D.R.m) (t : T0) : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t PP x : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  classical
  intro PP hPP x
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  let T : Finset (Pl D.host.E) := R.Sb ∪ R.Q t ∪ R.Q A.μ0
  have hQ : ∀ v ∈ R.Q t, v ∈ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hu : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).UnrAt v := fun v hv => by
    by_contra hn
    rcases (hL.Q_ram t v).1 hn with h | ⟨w, hw, h⟩
    · exact hv (Finset.mem_union_left _ (hQ v h))
    · refine hv (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hQ w hw, ?_⟩))
      have h1 : w = conjPrime₂ v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le (conjPrime₂ v).isPrime.ne_top fun c hc => by
        obtain ⟨c', hc', e⟩ := h c hc
        rw [mem_conjP, show cO D.host.E c = c' from RingOfIntegers.ext e.symm]
        exact hc')
      rw [h1, conjP_conjP]
  have hv : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).val v ∈ unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    by_cases hc : conjPrime₂ v = v
    · have h1 : (((R.xiH t).val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, TypeValues.val_sq_eq_one D.sp.cm (hL.xi_triv t) (hu v hv) hc, Units.val_one]
      show (((R.xiH t).val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    · have hs : ∀ S : Set (Pl D.host.E), (∀ w ∈ S, w ∈ T) → Bridge.SplitOff v S := fun S hS =>
        ⟨fun h => hc (HeightOneSpectrum.ext ((conjIdeal_asIdeal v).symm.trans h)),
          fun h => hv (Finset.mem_union_left _ (hS v h)), fun w hw h => hv (Finset.mem_union_right _ (Finset.mem_image.2
            ⟨w, hS w hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)), conjP_conjP]⟩))⟩
      have hS : ∀ w ∈ R.Sb, w ∈ T := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      obtain ⟨P, rfl⟩ := hon v (hs _ hS)
      have h1 : (R.C.mu0 i * R.xiH t).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i t P ((hok t P).2 (hs _ fun w hw => hw.elim (hS w) (hQ w)))⟩
      have h2 : (R.C.mu0 i * R.xiH A.μ0).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i A.μ0 P ((hok A.μ0 P).2 (hs _ fun w hw => hw.elim (hS w) fun h => Finset.mem_union_right _ h))⟩
      rw [hL.xi_base, mul_one] at h2
      rw [HChar.val_mul] at h1
      exact (mul_mem_cancel_left h2).1 h1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨a, k, hk, hx, hm⟩ := TypeValues.exists_lift_mem (R.xiH t) _ (T ∪ T.image conjPrime₂) (hL.xi_tame t)
    (TypeValues.inf_eq_one _ hn ho) hu hv (Finset.mem_union_left _ (hQ PP hPP)) x
  rw [hL.xiR t PP hPP a k x hk hx]
  exact hm

theorem placeEx (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ) (t : T0)
    {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) {gramR c0R c0L}
    (hj : R.models_jV)
    (hT : Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L)
    (hc : CoefficientBaseChange R i jL σ' (c0L i) c0')
    (hL : R.toLevCh.Is A.μ0) (hW : R.grp_chiW) (hon : R.fam_pl_onto) (hmu : R.fam_muVal) :
    PlaceEx R i t h c0' := by
  have h0 : CoefficientBaseChange R i (RingHom.id _) D.what₂.embLL (c0L i) (c0L i) := fun v => ⟨v, (MvPolynomial.map_id _).symm, rfl⟩
  have h1 := placeEx_of_type_mem R i (RingHom.id _) D.what₂.embLL t h (c0L i) hj hT h0
    (type_mem R i t _ (chiVal_of_chiW R hW i) (xiR_mem R hL hon hmu hT.ok i t))
  intro x₀
  obtain ⟨x, hx⟩ := h1 x₀
  choose y _ hy using hc
  exact ⟨fun k => y (x k), fun k => (hx k).trans (hy _).symm⟩

theorem placeEx_of_char (F : Face D A) (hR : R.Char F) (i : Fin D.R.m) {K' : Type} [Field K'] (jL : D.what₂.LL →+* K') (σ' : K' →+* ℂ)
    {v₀ : (R.MW i (sg0 D A)).Vec} {c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W}
    {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
    {M : ℕ} {Mh : Ideal (𝓞 D.host.E)} {lev : G → La →ₗ[𝓞 D.host.E] La} (hP : ThPinsR R i jL σ' v₀ c0' ι M Mh lev)
    (t : T0) {Cl : Type} [Fintype Cl] (h : Cl → GA D (Vc D i)) : PlaceEx R i t h c0' := by
  obtain ⟨_, _, _, hT, hc⟩ := hP.c0
  exact placeEx R i jL σ' t h c0' hR.models.jV hT hc hR.lev hR.grp.chiW hR.fam.pl_onto hR.fam.muVal

end GlobalTheory.RationalValues
