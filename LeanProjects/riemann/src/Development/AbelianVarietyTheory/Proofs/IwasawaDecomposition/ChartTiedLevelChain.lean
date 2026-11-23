import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Formalism.LocalToGlobal.Columns.RecLevelLocF
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
import Formalism.LocalToGlobal.Columns.AdelicLemmas

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.LevFun

section Res

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem hasRes_sub_lt {z : P.adicCompletion E} {r : 𝓞 E} (h : HasRes P z (Ideal.Quotient.mk P.asIdeal r)) :
    Valued.v (z - algebraMap E _ (algebraMap (𝓞 E) E r)) < 1 := by
  obtain ⟨r', e, hr⟩ := h
  have h1 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r') - algebraMap E _ (algebraMap (𝓞 E) E r)) < 1 := by
    rw [← map_sub, ← map_sub, valued_algebraMap, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.Quotient.eq.1 e
  have := Valuation.map_add_lt _ hr h1
  rwa [sub_add_sub_cancel] at this

theorem hasRes_congr {z z' : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c) (h' : Valued.v (z' - z) < 1) :
    HasRes P z' c := by
  obtain ⟨r, e, hr⟩ := h
  refine ⟨r, e, ?_⟩
  have := Valuation.map_add_lt _ h' hr
  rwa [sub_add_sub_cancel] at this

theorem valued_int_le (r : 𝓞 E) : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
  rw [valued_algebraMap]
  exact HeightOneSpectrum.valuation_le_one (K := E) P r

theorem hasRes_le {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c) : Valued.v z ≤ 1 := by
  obtain ⟨r, -, hr⟩ := h
  have := Valuation.map_add_le _ hr.le (valued_int_le (P := P) r)
  rwa [sub_add_cancel] at this

theorem hasRes_mul {z : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal} (h : HasRes P z c) (s : 𝓞 E) :
    HasRes P (algebraMap E _ (algebraMap (𝓞 E) E s) * z) (Ideal.Quotient.mk P.asIdeal s * c) := by
  obtain ⟨r, rfl, hr⟩ := h
  refine ⟨s * r, map_mul _ _ _, ?_⟩
  rw [map_mul, map_mul, ← mul_sub, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (valued_int_le s)) hr

end Res

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (𝓞 F)}

theorem adAt_eps (hov : IsOver v P) : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 := by
  have hm : Formalism.UG.P.afsplitEps E v ∈ Formalism.L2.Herm.intAf F E := Formalism.UG.P.afsplit_IE_int v _ (one_mem _)
  have h1 := PtExist.hasRes_redA P hm
  rw [redA_int P hm] at h1
  have h2 : resS F P ⟨_, hm⟩ = 1 := rll_rho_one v hov
  rw [h2] at h1
  have h3 := hasRes_sub_lt (r := 1) h1
  rw [map_one, map_one] at h3
  have h4 : adAt F P (Formalism.UG.P.afsplitEps E v) ≠ 0 := by
    intro h0
    rw [h0] at h3
    simp at h3
  have h5 := congrArg (adAt F P) (Formalism.UG.P.afsplit_eps_idem (E := E) v)
  rw [map_mul] at h5
  exact mul_left_cancel₀ h4 (h5.trans (mul_one _).symm)

theorem hasRes_rho (hov : IsOver v P) (w : AfE F E) (hw : prV (E := E) v w ∈ intV E v) :
    HasRes P (adAt F P w) (rll_rho v P ⟨_, hw⟩) := by
  have hm := Formalism.UG.P.afsplit_IE_int v _ hw
  have h1 := PtExist.hasRes_redA P hm
  rw [redA_int P hm] at h1
  have e : adAt F P (Formalism.UG.P.afsplitIE v (prV (E := E) v w)) = adAt F P w := by
    rw [Formalism.UG.P.afsplit_decomp, map_mul, adAt_eps hov, one_mul]
  rw [e] at h1
  exact h1

variable (hc : CMData F E) {n : ℕ} [NeZero n] {ST : Finset (HeightOneSpectrum (𝓞 E))} {π : 𝓞 E}

theorem exists_equiv (h : BasePi ST π) (hP : P ∈ ST) (hov : IsOver v P) {T : ℕ} (hT : T.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = T) (Λ : Submodule (intV E v) (Fin n → E ⊗[F] v.adicCompletion F))
    (hΛ : Λ = baseDualV hc n ST v) {M : Type} [AddCommGroup M] [Module (intV E v) M] (f : Λ →ₗ[intV E v] M) (hf : f ≠ 0)
    (hM : Nat.card M = T)
    (hL : ∀ x : Λ, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) (baseLb E n ST) → f x = 0)
    (hπ : ∀ (t t' : Λ), (t' : Fin n → E ⊗[F] v.adicCompletion F) = (fun a => inclE (F := F) (v.adicCompletion F) (π : E) * (t : Fin n → E ⊗[F] v.adicCompletion F) a) → f t' = 0) :
    ∃ e : M ≃+ (𝓞 E ⧸ P.asIdeal), ∀ (t : Λ) (hm : inclE (F := F) (v.adicCompletion F) (star (π : E)) * t.1 (lastIdx n) ∈ intV E v),
      e (f t) = rll_rho v P ⟨_, hm⟩ := by
  subst hΛ
  have hker : ∀ t, rll_psi hc n v h P t = 0 → f t = 0 := by
    intro t ht
    obtain ⟨w, hw, e⟩ := rll_rho_eq_zero v h (h.over_unique hc hP hov) _ ht
    replace e : inclE (F := F) (v.adicCompletion F) (star (π : E)) * t.1 (lastIdx n) =
      inclE (F := F) (v.adicCompletion F) (π : E) * w := e
    have hx : t.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star (π : E))) := by
      rw [← rll_dualV_eq hc n v h]; exact t.2
    rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
    have e0 : ∀ x, inclE (F := F) (v.adicCompletion F) (star (π : E)) *
        (inclE (F := F) (v.adicCompletion F) (star (π : E))⁻¹ * x) = x := fun x => by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h.star_ne_zero, map_one, one_mul]
    have e1 : ∀ x, inclE (F := F) (v.adicCompletion F) (star (π : E))⁻¹ *
        (inclE (F := F) (v.adicCompletion F) (star (π : E)) * x) = x := fun x => by
      rw [mul_left_comm, e0]
    have hm : (Pi.single (lastIdx n) (inclE (F := F) (v.adicCompletion F) (star (π : E))⁻¹ * w) :
        Fin n → E ⊗[F] v.adicCompletion F) ∈ baseDualV hc n ST v := by
      rw [rll_dualV_eq hc n v h, rll_mem_loc_dLat n v _ h.star_ne_zero]
      refine ⟨fun i hi => by rw [Pi.single_eq_of_ne hi]; exact zero_mem _, ?_⟩
      rw [Pi.single_eq_same]
      exact (e0 w).symm ▸ hw
    have h1 := hπ ⟨_, hm⟩ ((⟨_, rll_incl_int v π⟩ : intV E v) • (⟨_, hm⟩ : baseDualV hc n ST v)) rfl
    have h2 := hL (t - (⟨_, rll_incl_int v π⟩ : intV E v) • (⟨_, hm⟩ : baseDualV hc n ST v)) (by
      rw [rll_baseLb_eq n h]
      refine (rll_mem_loc_dLat n v _ (inv_ne_zero h.coe_ne_zero) _).2 ⟨fun i hi => ?_, ?_⟩
      · show t.1 i - inclE (F := F) (v.adicCompletion F) (π : E) * (Pi.single (lastIdx n)
          (inclE (F := F) (v.adicCompletion F) (star (π : E))⁻¹ * w) : Fin n → E ⊗[F] v.adicCompletion F) i ∈ _
        rw [Pi.single_eq_of_ne hi, mul_zero, sub_zero]
        exact hx.1 i hi
      · show _ * (t.1 (lastIdx n) - inclE (F := F) (v.adicCompletion F) (π : E) * (Pi.single (lastIdx n)
          (inclE (F := F) (v.adicCompletion F) (star (π : E))⁻¹ * w) : Fin n → E ⊗[F] v.adicCompletion F) (lastIdx n)) ∈ _
        rw [Pi.single_eq_same, mul_left_comm, ← e, e1, sub_self, mul_zero]
        exact zero_mem _)
    rwa [map_sub, h1, sub_zero] at h2
  have hsurj := rll_psi_surj hc n v h hov
  let g : (𝓞 E ⧸ P.asIdeal) →+ M :=
    (rll_psi hc n v h P).liftOfSurjective hsurj ⟨f.toAddMonoidHom, fun t ht => hker t ht⟩
  have hg : ∀ t, g (rll_psi hc n v h P t) = f t := fun t =>
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  haveI : Fact T.Prime := ⟨hT⟩
  haveI : Finite M := Nat.finite_of_card_ne_zero (hM ▸ hT.ne_zero)
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (hcard ▸ hT.ne_zero)
  have hinj : Function.Injective g := by
    rw [← AddMonoidHom.ker_eq_bot_iff]
    haveI : Fact (Nat.card (𝓞 E ⧸ P.asIdeal)).Prime := ⟨hcard ▸ hT⟩
    refine (AddSubgroup.eq_bot_or_eq_top_of_prime_card g.ker).resolve_right fun h0 => hf ?_
    ext t
    rw [← hg]
    exact (h0.ge (AddSubgroup.mem_top _) : _ ∈ g.ker)
  have hbij : Function.Bijective g := hinj.bijective_of_nat_card_le (by rw [hM, hcard])
  refine ⟨(AddEquiv.ofBijective g hbij).symm, fun t hm => ?_⟩
  rw [AddEquiv.symm_apply_eq]
  exact (hg t).symm

theorem f_eq_rho (h : BasePi ST π) (hP : P ∈ ST) (hov : IsOver v P) {SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {p : DecoF E n ST SG Q} {y k : GL (Fin n) (AfE F E)} (hp : IsPtOf hc (y * k) p)
    (hk : ∀ j, HasRes P (adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 (lastIdx n) j))
      (if j = lastIdx n then Ideal.Quotient.mk P.asIdeal (cO E π) else 0))
    (z : Fin n → E) (s : 𝓞 E) (hs : s • z ∈ p.deco.1.N)
    (hz : ((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈ baseDualV hc n ST v)
    (hm : inclE (F := F) (v.adicCompletion F) (star (π : E)) *
      (((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a))) (lastIdx n) ∈ intV E v) :
    p.deco.1.f ⟨P, hP⟩ (s • z) = Ideal.Quotient.mk P.asIdeal s * rll_rho v P ⟨_, hm⟩ := by
  have h1 := hp.f ⟨P, hP⟩ _ hs (lastIdx n) (by have := NeZero.pos n; simp [lastIdx]; omega)
  have ew : ∀ j, (((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a))) j =
      prV (E := E) v (Col2.pullV y z j) := fun j => by
    rw [← map_inv]
    simp only [Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  rw [rll_dualV_eq hc n v h, rll_mem_loc_dLat n v _ h.star_ne_zero] at hz
  have hint : ∀ j, prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (star (π : E)) * Col2.pullV y z j) ∈ intV E v := fun j => by
    rw [map_mul, ← ew]
    by_cases hj : j = lastIdx n
    · rw [hj]; exact hm
    · exact mul_mem (rll_incl_int v (cO E π)) (hz.1 j hj)
  have hu : Valued.v (algebraMap E (P.adicCompletion E) (star (π : E))) = 1 := by
    rw [valued_algebraMap]
    exact CharValCompare.val_of_notMem (h.conj_notMem hP)
  have hle : ∀ j, Valued.v (adAt F P (Col2.pullV y z j)) ≤ 1 := fun j => by
    have := hasRes_le (hasRes_rho hov _ (hint j))
    rwa [map_mul, map_mul, adAt_inclE, hu, one_mul] at this
  have h2 := hasRes_rho hov _ (hint (lastIdx n))
  have e2 : (⟨_, hint (lastIdx n)⟩ : intV E v) = ⟨_, hm⟩ := Subtype.ext (by
    show prV (E := E) v _ = _ * _
    rw [map_mul, ← ew]; rfl)
  rw [e2, map_mul, adAt_inclE] at h2
  refine h1.unique (hasRes_congr (hasRes_mul h2 s) ?_)
  have e3 : Col2.pullV (y * k) (s • z) (lastIdx n) = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (s : E) *
      ∑ j, (k⁻¹ : GL (Fin n) (AfE F E)).1 (lastIdx n) j * Col2.pullV y z j := by
    unfold Col2.pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    have : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((s • z) i)) =
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (s : E) • fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z i) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, map_mul, smul_eq_mul]
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rfl
  have e4 : algebraMap E (P.adicCompletion E) (star (π : E)) * adAt F P (Col2.pullV y z (lastIdx n)) =
      ∑ j, algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (if j = lastIdx n then cO E π else 0)) *
        adAt F P (Col2.pullV y z j) := by
    rw [Finset.sum_eq_single (lastIdx n) (fun j _ hj => by rw [if_neg hj, map_zero, map_zero, zero_mul])
      (fun hh => absurd (Finset.mem_univ _) hh), if_pos rfl]
    rfl
  show Valued.v (adAt F P _ - _) < 1
  rw [e3, e4, map_mul, adAt_inclE, ← mul_sub, map_sum, ← Finset.sum_sub_distrib, map_mul]
  refine lt_of_le_of_lt (mul_le_of_le_one_left' (valued_int_le s)) (Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_)
  rw [map_mul, ← _root_.sub_mul, map_mul]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' (hle j)) (hasRes_sub_lt ?_)
  have := hk j
  split_ifs at this ⊢
  · exact this
  · rwa [map_zero]

theorem exists_equiv_level {T f₀ : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {J : Matrix (Fin n) (Fin n) E}
    (S : StepLevel F E hc.sig J T f₀ bad) (hJ : J = 1) (hLb : S.Lb = baseLb E n ST) (h : BasePi ST π) (hP : P ∈ ST)
    (hv : (T : 𝓞 F) ∈ v.asIdeal) (hov : IsOver v P) (hT : T.Prime) (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = T)
    (hπ : ∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)),
      t'.1 = (fun a => inclE (F := F) (v.adicCompletion F) (π : E) * t.1 a) → S.fT v hv t' = 0) :
    ∃ e : S.fM v hv ≃+ (𝓞 E ⧸ P.asIdeal),
      (∀ {SG Q : Finset (HeightOneSpectrum (𝓞 E))} (p : DecoF E n ST SG Q) (y k : GL (Fin n) (AfE F E)), IsPtOf hc (y * k) p →
        (∀ r j : Fin n, r.1 + 1 = n → HasRes P (adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j))
          (if j = r then Ideal.Quotient.mk P.asIdeal (cO E π) else 0)) →
        ∀ (z : Fin n → E) (s : 𝓞 E), s • z ∈ p.deco.1.N →
        ∀ hz : ((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) ∈
          latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)),
        p.deco.1.f ⟨P, hP⟩ (s • z) = Ideal.Quotient.mk P.asIdeal s * e (S.fT v hv ⟨_, hz⟩)) ∧
      ∀ (x : Fin n → E) (j : Fin n) (r : 𝓞 E)
        (t : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb))),
        j.1 + 1 = n → t.1 = (fun s => inclE (F := F) (v.adicCompletion F) (x s)) → (r : E) = star (π : E) * x j →
        e (S.fT v hv t) = Ideal.Quotient.mk P.asIdeal r := by
  subst hJ
  have hΛ : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) 1 S.Lb)) =
      baseDualV hc n ST v := by rw [hLb]
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = lastIdx n := fun j => by
    have := NeZero.pos n
    rw [Fin.ext_iff]; simp only [lastIdx]; omega
  obtain ⟨e, he⟩ := exists_equiv hc h hP hov hT hcard _ hΛ (S.fT v hv) (S.fT_ne v hv) (S.fM_card v hv)
    (fun x hx => S.fT_L v hv x ((congrArg (latS (F := F) (v.adicCompletion F) (intV E v)) hLb).ge hx)) hπ
  refine ⟨e, fun p y k hp hk z s hs hz => ?_, fun x j r t hj ht hr => ?_⟩
  · have hz' := hΛ ▸ hz
    have hm := rll_last_mem hc n v h ⟨_, hz'⟩
    rw [he ⟨_, hz⟩ hm]
    exact f_eq_rho hc h hP hov hp (fun j => hk _ j ((hlast _).2 rfl)) z s hs hz' hm
  · obtain rfl := (hlast j).1 hj
    have e1 : inclE (F := F) (v.adicCompletion F) (star (π : E)) * t.1 (lastIdx n) =
        inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r) * ((1 : intV E v) : E ⊗[F] v.adicCompletion F) := by
      rw [ht, ← map_mul, ← hr]
      exact (mul_one _).symm
    have hm : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E r) * ((1 : intV E v) : E ⊗[F] v.adicCompletion F) ∈
        intV E v := mul_mem (rll_incl_int _ r) (one_mem _)
    refine (he t (e1 ▸ hm)).trans ?_
    refine (congrArg (rll_rho v P) (Subtype.ext e1 : _ = ⟨_, hm⟩)).trans ?_
    rw [rll_rho_incl_mul, rll_rho_one _ hov, mul_one]

end Loc

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem dualL_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E)
    {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : Formalism.L2.Forms.dualL (hc.sig : E →+* E) 1 L = Formalism.HermitianLatticesTheory.dual (hStd E n) L := by
  unfold Formalism.L2.Forms.dualL
  rw [← Submodule.span_eq (Formalism.HermitianLatticesTheory.dual (hStd E n) L)]
  congr 1
  ext y
  rw [SetLike.mem_coe, mem_dual]
  show (∀ x ∈ L, hform (hc.sig : E →+* E) 1 x y ∈ (algebraMap (𝓞 E) E).range) ↔ _
  refine forall_congr' fun x => forall_congr' fun _ => ?_
  rw [Formalism.L2.Col.hform_one, Submodule.mem_one]
  rfl

theorem mem_baseL {B : Base} {n : ℕ} [NeZero n] {ST : Finset (HeightOneSpectrum (𝓞 B.host.E))} {π : 𝓞 B.host.E}
    (h : BasePi ST π) (x : Fin n → B.host.E) : x ∈ baseL B n π ↔ x ∈ baseLb B.host.E n ST := by
  have hl : ∀ j : Fin n, j.1 + 1 = n ↔ j = lastIdx n := fun j => by
    have := NeZero.pos n
    rw [Fin.ext_iff]; simp only [lastIdx]; omega
  rw [rll_mem_baseLb]
  constructor
  · intro hx
    choose r hr using hx
    exact ⟨r, fun j => (hr j).1.symm, fun P hP => (h.dvd _).2 ((hr _).2 ((hl _).2 rfl)) P hP⟩
  · rintro ⟨r, hr, hP⟩ j
    exact ⟨r j, (hr j).symm, fun hj => by rw [(hl j).1 hj]; exact (h.dvd _).1 hP⟩

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet E n ST SG) {a : 𝓞 E} (ha : SepElt ST a) (P : ST) (z : Fin n → E) (hz : z ∈ d.1.Lsh) :
    ∃ s : 𝓞 E, Ideal.Quotient.mk P.1.asIdeal s ≠ 0 ∧ s • z ∈ d.1.N := by
  obtain ⟨s, hs, hsz⟩ := (mem_locP _ _ _).1 (d.2.Lsh_le_at ha P hz)
  exact ⟨s, fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0), hsz⟩

theorem fv_of_smul {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {T : ℕ}
    {res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v} {i : ℕ} {hi : i ≤ D.R.m}
    {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)} (L : LevelCompatibleLattices M T res i hi lat) (v : A.vT) (c : C.cls i)
    (z : LdG D i hi (lat c)) (s : 𝓞 D.host.E) (hs : res v s ≠ 0) (w : A.Fv v)
    (h : M.fv i v c (L.pr v c ⟨_, Submodule.smul_mem _ s z.2⟩) = res v s * w) : M.fv i v c (L.pr v c z) = w := by
  have h1 : L.pr v c ⟨_, Submodule.smul_mem _ s z.2⟩ = res v s • L.pr v c z := L.pr_smul v c s z
  rw [h1, map_smul, smul_eq_mul] at h
  exact mul_left_cancel₀ hs h

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fvTieG : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdV l u a eV → I.IdL l Z u a i hi L → (∀ (β : Ch) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) (t t' : latS (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E v) (Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (K β).lev.Lb))), t'.1 = (fun a => inclE (F := (I.rec7 l Z).host.F) (v.adicCompletion (I.rec7 l Z).host.F) (show (I.rec7 l Z).host.E from ((X.piT u : 𝓞 B.host.E) : B.host.E)) * t.1 a) → (K β).lev.fT v h t' = 0) → ∃ fMe, FvTieG L eV K fMe ∧ ∀ β v (x : Fin (B.R.N i) → (I.rec7 l Z).host.E) (j : Fin (B.R.N i)) (r : 𝓞 B.host.E) (t : latS (F := (I.rec7 l Z).host.F) ((eV v).1.adicCompletion (I.rec7 l Z).host.F) (intV (I.rec7 l Z).host.E (eV v).1) (Submodule.span (𝓞 (I.rec7 l Z).host.E) (dualSet (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) (K β).lev.Lb))), j.1 + 1 = B.R.N i → t.1 = (fun s => inclE (F := (I.rec7 l Z).host.F) ((eV v).1.adicCompletion (I.rec7 l Z).host.F) (x s)) → (r : B.host.E) = B.host.conj (X.piT u : B.host.E) * (show B.host.E from x j) → fMe β v ((K β).lev.fT (eV v).1 (eV v).2 t) = I.resT l u a v r := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eV L hK hV hL hS
  obtain ⟨k, hR⟩ := hK
  have hB : BasePi ((B.primes X).vT u) (X.piT u) := basePi_of_ok (base_fields_primes_ok B X).1 l.pr u
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have hcrd := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hJ := hcrd.1
  have hlat := fun c => ((hcrd.2.2 u a).1 c)
  have hLb : ∀ β, (K β).lev.Lb = baseLb B.fields.E (B.R.N i) ((B.primes X).vT u) := fun β =>
    Submodule.ext fun x => (hR.lb β x).trans (mem_baseL hB x)
  have hW := @exists_equiv_level (I.rec7 l Z).host.F (I.rec7 l Z).host.E _ _ _ _ _ _
  have hE := fun β (v : (I.atT l u a).vT) => hW
    (I.rec7 l Z).sp.cm (n := B.R.N i) (ST := (B.primes X).vT u) (π := X.piT u) (P := v.1)
    (K β).lev hJ (hLb β) hB v.2 (eV v).2 (congrArg HeightOneSpectrum.asIdeal (hV v)) (l.pr.T_prime u) (l.pr.vT_norm u v.1 v.2)
    (hS β _ _)
  choose e he1 he2 using hE
  refine ⟨e, ?_, ?_⟩
  swap
  · intro β v x j r t hj ht hr
    rw [← bridge_star_holds B.R B.host] at hr
    exact he2 β v x j r t hj ht hr
  rintro v β ⟨c, rfl⟩ z hz
  have hz1 : z.1 ∈ ((I.stp u a i).rep c).1.1.deco.1.Lsh :=
    ((congrArg₂ (Formalism.L2.Forms.dualL (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)) hJ (hlat c)).trans
      (dualL_one (I.rec7 l Z).sp.cm _)).le z.2
  have h0 := exists_smul_mem ((I.stp u a i).rep c).1.1.deco (sepElt_of_ok l.pr u) v z.1 hz1
  obtain ⟨s, h6, hsz⟩ := h0
  have h5 := (fv_te_laws ((I.atIn u a).A i) (B.T u) ((l.ch u a).step i) ((l.lev u a).lev i)).1 v c ⟨_, hsz⟩
  have h2 := he1 (chOf c) v (extTo I.SQ ((I.stp u a i).rep c).1.1) ((K (chOf c)).y ⟨c, rfl⟩).1 (k (chOf c)) (hR.pt c) (hR.k_T (chOf c) v) z.1 s hsz hz
  have h3 := hL.1 v c ⟨_, Submodule.smul_mem (LdG (I.rec7 l Z) i hi _) s z.2⟩ hsz
  exact fv_of_smul L v c z s h6 _ ((congrArg ((I.fm l u a).fv i v c) h3).trans (h5.trans h2))

end GlobalTheory.Mem.Col2.LevFun
