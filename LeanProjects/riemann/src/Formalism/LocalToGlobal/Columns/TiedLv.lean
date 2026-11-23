import Formalism.LocalToGlobal.Columns.TiedAtT
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
  {M M' : Submodule (𝓞 E) (Sp E n)} {s t : 𝓞 E}

def lvPr (hs : ∀ x ∈ M', s • x ∈ M) (t : 𝓞 E) : ↥M' →ₗ[𝓞 E] modP P M :=
  (modP.mk P M).comp
    ({ toFun := fun z => ⟨t • s • z.1, M.smul_mem t (hs z.1 z.2)⟩
       map_add' := fun x y => Subtype.ext (by simp only [Submodule.coe_add, smul_add])
       map_smul' := fun r x => Subtype.ext (by
        show t • s • r • x.1 = r • t • s • x.1
        rw [smul_comm s r, smul_comm t r]) } : ↥M' →ₗ[𝓞 E] ↥M)

theorem lvPr_apply (hs : ∀ x ∈ M', s • x ∈ M) (z : ↥M') :
    lvPr P hs t z = modP.mk P M ⟨t • s • z.1, M.smul_mem t (hs z.1 z.2)⟩ := rfl

theorem lv_mk_eq_zero (x : ↥M) : modP.mk P M x = 0 ↔ x.1 ∈ P.asIdeal • M := by
  simp only [modP.mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff]

theorem lv_mk_eq_iff (x y : ↥M) : modP.mk P M x = modP.mk P M y ↔ x.1 - y.1 ∈ P.asIdeal • M := by
  rw [← sub_eq_zero, ← map_sub, lv_mk_eq_zero, Submodule.coe_sub]

theorem lvPr_of_mem (hs : ∀ x ∈ M', s • x ∈ M) (hst : s * t - 1 ∈ P.asIdeal) (z : ↥M') (hz : z.1 ∈ M) :
    lvPr P hs t z = modP.mk P M ⟨z.1, hz⟩ := by
  rw [lvPr_apply, lv_mk_eq_iff]
  have e : t • s • z.1 - z.1 = (s * t - 1) • z.1 := by
    rw [sub_smul, one_smul, mul_smul, smul_comm s t]
  rw [e]
  exact Submodule.smul_mem_smul hst hz

theorem lvPr_surjective (hle : M ≤ M') (hs : ∀ x ∈ M', s • x ∈ M) (hst : s * t - 1 ∈ P.asIdeal) :
    Function.Surjective (lvPr P hs t) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨⟨x.1, hle x.2⟩, lvPr_of_mem P hs hst _ x.2⟩

theorem lvPr_eq_zero (hle : M ≤ M') (hs : ∀ x ∈ M', s • x ∈ M) (hst : s * t - 1 ∈ P.asIdeal) (z : ↥M') :
    lvPr P hs t z = 0 ↔ z.1 ∈ P.asIdeal • M' := by
  have key : ∀ w ∈ P.asIdeal • M', s • w ∈ P.asIdeal • M := by
    intro w hw
    refine Submodule.smul_induction_on hw (fun r hr n hn => ?_) (fun x y hx hy => ?_)
    · rw [smul_comm]
      exact Submodule.smul_mem_smul hr (hs n hn)
    · rw [smul_add]
      exact Submodule.add_mem _ hx hy
  rw [lvPr_apply, lv_mk_eq_zero]
  constructor
  · intro h
    have h1 : t • s • z.1 ∈ P.asIdeal • M' := Submodule.smul_mono le_rfl hle h
    have h2 : (s * t - 1) • z.1 ∈ P.asIdeal • M' := Submodule.smul_mem_smul hst z.2
    have e : z.1 = t • s • z.1 - (s * t - 1) • z.1 := by
      rw [sub_smul, one_smul, mul_smul, smul_comm s t]
      abel
    rw [e]
    exact Submodule.sub_mem _ h1 h2
  · intro h
    exact Submodule.smul_mem _ t (key _ h)

theorem lvPr_smul (hs : ∀ x ∈ M', s • x ∈ M) (r : 𝓞 E) (z : ↥M') :
    lvPr P hs t (r • z) = Ideal.Quotient.mk P.asIdeal r • lvPr P hs t z := by
  rw [map_smul]
  generalize lvPr P hs t z = q
  induction q using Submodule.Quotient.induction_on with
  | H x => rw [Module.Quotient.mk_smul_mk, Submodule.Quotient.mk_smul]

theorem lv_exists_inv {a : 𝓞 E} (ha : a ∉ P.asIdeal) : ∃ t : 𝓞 E, a * t - 1 ∈ P.asIdeal := by
  haveI := P.isMaximal
  have h0 : Ideal.Quotient.mk P.asIdeal a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (Ideal.Quotient.mk P.asIdeal a)⁻¹
  refine ⟨t, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, ht, mul_inv_cancel₀ h0, sub_self]

end Pr

section Dec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  (d : DecoSet E n ST SG) {a : 𝓞 E} (ha : SepElt ST a) (P : ST)

include ha in

theorem lv_LshKer_eq : d.1.LshKer P = d.1.L ⊔ P.1.asIdeal • d.1.Lsh := by
  classical
  apply le_antisymm
  · intro z hz
    obtain ⟨h1, h2⟩ := (d.2.mem_LshKer ha P z).1 hz
    obtain ⟨c, hc⟩ := lv_exists_inv P.1 (ha.off P)
    obtain ⟨b, hb⟩ := crtPl ST (fun R => if R = P.1 then c else 0)
    have hbP : b - c ∈ P.1.asIdeal := by
      have := hb P.1 P.2
      rwa [if_pos rfl] at this
    have hbQ : ∀ Q : ST, Q ≠ P → b ∈ Q.1.asIdeal := by
      intro Q hQ
      have := hb Q.1 Q.2
      rwa [if_neg (fun e => hQ (Subtype.ext e)), sub_zero] at this
    have he : a * b - 1 ∈ P.1.asIdeal := by
      have : a * b - 1 = a * (b - c) + (a * c - 1) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hbP) hc
    have hL : (a * b) • z ∈ d.1.L := by
      rw [d.2.mem_L]
      refine ⟨?_, fun Q => ?_⟩
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_mem _ b (d.2.smul_Lsh_mem_N ha.conj h1)
      · rw [d.2.f_smul Q (a * b) z (d.2.Lsh_le_at ha Q h1)]
        by_cases hQ : Q = P
        · subst hQ
          rw [h2, mul_zero]
        · rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ a (hbQ Q hQ)), zero_mul]
    have e : z = (a * b) • z + (-(a * b - 1)) • z := by
      rw [← add_smul]
      have : a * b + -(a * b - 1) = 1 := by ring
      rw [this, one_smul]
    rw [e]
    exact Submodule.add_mem_sup hL (Submodule.smul_mem_smul (neg_mem he) h1)
  · refine sup_le (fun x hx => (d.2.mem_LshKer ha P x).2 ⟨d.2.L_le_Lsh hx, ((d.2.mem_L x).1 hx).2 P⟩) ?_
    rw [Submodule.smul_le]
    intro r hr x hx
    refine (d.2.mem_LshKer ha P _).2 ⟨Submodule.smul_mem _ r hx, ?_⟩
    rw [d.2.f_smul P r x (d.2.Lsh_le_at ha P hx), Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]

def dPr (t : 𝓞 E) : ↥d.1.Lsh →ₗ[𝓞 E] d.lv P :=
  lvPr P.1 (M := d.1.N) (M' := d.1.Lsh) (s := a) (fun _ hx => d.2.smul_Lsh_mem_N ha.conj hx) t

include ha in
theorem lv_smul_LshKer_mem {x : Sp E n} (hx : x ∈ d.1.LshKer P) : a • x ∈ d.1.kerAt P := by
  have key : d.1.LshKer P ≤ (d.1.kerAt P).comap (LinearMap.lsmul (𝓞 E) (Sp E n) a) := by
    unfold Deco.LshKer
    rw [Submodule.span_le]
    rintro y ⟨hy, hfy⟩
    show a • y ∈ d.1.kerAt P
    unfold Deco.kerAt
    apply Submodule.subset_span
    refine ⟨d.2.smul_Lsh_mem_N ha.conj hy, ?_⟩
    rw [d.2.f_smul P a y (d.2.Lsh_le_at ha P hy), hfy, mul_zero]
  exact key hx

include ha in
theorem lv_kerAt_le : d.1.kerAt P ≤ d.1.LshKer P := by
  unfold Deco.kerAt Deco.LshKer
  exact Submodule.span_mono fun x hx => ⟨d.2.N_le_Lsh hx.1, hx.2⟩

def dPrk (t : 𝓞 E) : ↥(d.1.LshKer P) →ₗ[𝓞 E] d.lk P :=
  lvPr P.1 (M := d.1.kerAt P) (M' := d.1.LshKer P) (s := a) (fun _ hx => lv_smul_LshKer_mem d ha P hx) t

variable {t : 𝓞 E} (hat : a * t - 1 ∈ P.1.asIdeal)

include hat in

theorem fv_dPr (z : ↥d.1.Lsh) : d.fv P (dPr d ha P t z) = d.1.f P z.1 := by
  unfold DecoSet.fv dPr
  rw [lvPr_apply, modP.lift_mk]
  show d.1.f P (t • a • z.1) = d.1.f P z.1
  have hz : z.1 ∈ d.1.at P.1 := d.2.Lsh_le_at ha P z.2
  rw [d.2.f_smul P t _ (Submodule.smul_mem _ a hz), d.2.f_smul P a _ hz, ← mul_assoc, ← map_mul]
  have h1 : Ideal.Quotient.mk P.1.asIdeal (t * a) = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.1.asIdeal), Ideal.Quotient.eq, mul_comm]
    exact hat
  rw [h1, one_mul]

include hat in

theorem dPrk_te {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (z : Sp E n) (hz : z ∈ d.1.Lsh) (hf : d.1.f P z = 1)
    (h : q • z ∈ d.1.LshKer P) : dPrk d ha P t ⟨q • z, h⟩ = d.te P q := by
  have hm : q • d.e1 P ∈ d.1.kerAt P := d.2.smul_mem_kerAt P hq (d.first_raising_mem_equivariant P)
  have h1 : d.te P q = dPrk d ha P t ⟨q • d.e1 P, lv_kerAt_le d ha P hm⟩ := by
    unfold DecoSet.te
    rw [dif_pos hm]
    exact (lvPr_of_mem P.1 (M := d.1.kerAt P) (M' := d.1.LshKer P) (fun _ hx => lv_smul_LshKer_mem d ha P hx) hat
      ⟨q • d.e1 P, lv_kerAt_le d ha P hm⟩ hm).symm
  rw [h1, ← sub_eq_zero, ← map_sub]
  refine (lvPr_eq_zero P.1 (lv_kerAt_le d ha P) _ hat _).2 ?_
  show q • z - q • d.e1 P ∈ _
  rw [← smul_sub]
  refine Submodule.smul_mem_smul hq ((d.2.mem_LshKer ha P _).2 ⟨Submodule.sub_mem _ hz (d.2.N_le_Lsh (d.first_raising_mem_equivariant P)), ?_⟩)
  have e : z - d.e1 P = z + (-1 : 𝓞 E) • d.e1 P := by rw [neg_smul, one_smul, sub_eq_add_neg]
  have he1 : d.e1 P ∈ d.1.at P.1 := le_locP _ _ (d.first_raising_mem_equivariant P)
  rw [e, d.2.f_add P z (d.2.Lsh_le_at ha P hz) _ (Submodule.smul_mem _ _ he1), d.2.f_smul P (-1) _ he1, hf, d.functional_firstBasis_eq_one, map_neg,
    map_one]
  ring

end Dec

section Comparison₂

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word) {n : ℕ} [NeZero n]
  {cls : Type} (s : cls → DecoSet X.E n (Pr.vT u) Pr.vGs) (Q : StepCrd Pr σ₀ n fun c => (s c).1.L)

theorem tie_Ld_eq (c : cls) : Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) = (s c).1.Lsh := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact rlc_span_dualSet hc n _

include hPr in

theorem tie_Lk_eq (c : cls) (P : Pr.vT u) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) :
    Q.lat c ⊔ I • Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) = (s c).1.LshKer P := by
  rw [tie_Ld_eq, hI, lv_LshKer_eq (s c) (sepElt_of_ok hPr u) P, Q.hlat]

def tieInv (P : Pr.vT u) : 𝓞 X.E := (lv_exists_inv P.1 ((sepElt_of_ok hPr u).off P)).choose

theorem tieInv_spec (P : Pr.vT u) : cO X.E (Pr.piT u) * tieInv hPr u P - 1 ∈ P.1.asIdeal := by
  unfold tieInv
  exact (lv_exists_inv P.1 ((sepElt_of_ok hPr u).off P)).choose_spec

def tiePr (P : Pr.vT u) (c : cls) :
    ↥(Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) →+ (s c).lv P :=
  ((dPr (s c) (sepElt_of_ok hPr u) P (tieInv hPr u P)).comp
    (Submodule.inclusion (le_of_eq (tie_Ld_eq hc σ₀ u s Q c)))).toAddMonoidHom

def tiePrk (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) :
    ↥(Q.lat c ⊔ I • Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) →+ (s c).lk P :=
  ((dPrk (s c) (sepElt_of_ok hPr u) P (tieInv hPr u P)).comp
    (Submodule.inclusion (le_of_eq (tie_Lk_eq hc hPr σ₀ u s Q c P I hI)))).toAddMonoidHom

theorem tiePr_surj (P : Pr.vT u) (c : cls) : Function.Surjective (tiePr hc hPr σ₀ u s Q P c) := by
  have hsurj : Function.Surjective (dPr (s c) (sepElt_of_ok hPr u) P (tieInv hPr u P)) :=
    lvPr_surjective P.1 (s c).2.N_le_Lsh _ (tieInv_spec hPr u P)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨⟨x.1, by rw [tie_Ld_eq hc σ₀ u s Q c]; exact x.2⟩, ?_⟩
  exact hx

theorem tiePr_smul (P : Pr.vT u) (c : cls) (r : 𝓞 X.E) (z) :
    tiePr hc hPr σ₀ u s Q P c (r • z) = Ideal.Quotient.mk P.1.asIdeal r • tiePr hc hPr σ₀ u s Q P c z := by
  have e : Submodule.inclusion (le_of_eq (tie_Ld_eq hc σ₀ u s Q c)) (r • z) =
      r • Submodule.inclusion (le_of_eq (tie_Ld_eq hc σ₀ u s Q c)) z := map_smul _ _ _
  simp only [tiePr, LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply, e]
  exact lvPr_smul _ _ _ _

theorem tiePr_ker (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) (z) :
    tiePr hc hPr σ₀ u s Q P c z = 0 ↔ z.1 ∈ I • Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) := by
  subst hI
  exact (lvPr_eq_zero P.1 (s c).2.N_le_Lsh (fun _ hx => (s c).2.smul_Lsh_mem_N (sepElt_of_ok hPr u).conj hx) (tieInv_spec hPr u P)
    (Submodule.inclusion (le_of_eq (tie_Ld_eq hc σ₀ u s Q c)) z)).trans
    (Iff.of_eq (congrArg (fun S => z.1 ∈ P.1.asIdeal • S) (tie_Ld_eq hc σ₀ u s Q c)).symm)

theorem tie_fv (P : Pr.vT u) (c : cls) (z) : (s c).fv P (tiePr hc hPr σ₀ u s Q P c z) = (s c).1.f P z.1 := by
  exact fv_dPr (s c) (sepElt_of_ok hPr u) P (tieInv_spec hPr u P) _

theorem tie_fv_ker (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) (z) :
    (s c).fv P (tiePr hc hPr σ₀ u s Q P c z) = 0 ↔
      z.1 ∈ Q.lat c ⊔ I • Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c) := by
  have hz : z.1 ∈ (s c).1.Lsh := by
    rw [← tie_Ld_eq hc σ₀ u s Q c]
    exact z.2
  rw [tie_fv, tie_Lk_eq hc hPr σ₀ u s Q c P I hI, (s c).2.mem_LshKer (sepElt_of_ok hPr u) P]
  exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩

theorem tiePrk_surj (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) :
    Function.Surjective (tiePrk hc hPr σ₀ u s Q P c I hI) := by
  intro y
  obtain ⟨x, hx⟩ := lvPr_surjective P.1 (lv_kerAt_le (s c) (sepElt_of_ok hPr u) P)
    (fun _ hx => lv_smul_LshKer_mem (s c) (sepElt_of_ok hPr u) P hx) (tieInv_spec hPr u P) y
  refine ⟨⟨x.1, by rw [tie_Lk_eq hc hPr σ₀ u s Q c P I hI]; exact x.2⟩, ?_⟩
  exact hx

theorem tiePrk_smul (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) (r : 𝓞 X.E) (z) :
    tiePrk hc hPr σ₀ u s Q P c I hI (r • z) = Ideal.Quotient.mk P.1.asIdeal r • tiePrk hc hPr σ₀ u s Q P c I hI z := by
  have e : Submodule.inclusion (le_of_eq (tie_Lk_eq hc hPr σ₀ u s Q c P I hI)) (r • z) =
      r • Submodule.inclusion (le_of_eq (tie_Lk_eq hc hPr σ₀ u s Q c P I hI)) z := map_smul _ _ _
  simp only [tiePrk, LinearMap.toAddMonoidHom_coe, LinearMap.coe_comp, Function.comp_apply, e]
  exact lvPr_smul _ _ _ _

theorem tiePrk_ker (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal) (z) :
    tiePrk hc hPr σ₀ u s Q P c I hI z = 0 ↔
      z.1 ∈ I • (Q.lat c ⊔ I • Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) := by
  subst hI
  exact (lvPr_eq_zero P.1 (lv_kerAt_le (s c) (sepElt_of_ok hPr u) P) (fun _ hx => lv_smul_LshKer_mem (s c) (sepElt_of_ok hPr u) P hx)
    (tieInv_spec hPr u P) (Submodule.inclusion (le_of_eq (tie_Lk_eq hc hPr σ₀ u s Q c P _ rfl)) z)).trans
    (Iff.of_eq (congrArg (fun S => z.1 ∈ P.1.asIdeal • S) (tie_Lk_eq hc hPr σ₀ u s Q c P _ rfl)).symm)

theorem tiePrk_te (P : Pr.vT u) (c : cls) (I : Ideal (𝓞 X.E)) (hI : I = P.1.asIdeal)
    (z : ↥(Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)))
    (hz : (s c).fv P (tiePr hc hPr σ₀ u s Q P c z) = 1)
    (h : (Pr.T u : 𝓞 X.E) • z.1 ∈ Q.lat c ⊔ I • Formalism.L2.Forms.dualL (hc.sig : X.E →+* X.E) Q.J (Q.lat c)) :
    tiePrk hc hPr σ₀ u s Q P c I hI ⟨_, h⟩ = (s c).te P (Pr.T u : 𝓞 X.E) := by
  rw [tie_fv] at hz
  exact dPrk_te (s c) (sepElt_of_ok hPr u) P (tieInv_spec hPr u P) (T_mem hPr u P) z.1
    ((tie_Ld_eq hc σ₀ u s Q c) ▸ z.2) hz _

end Comparison₂

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem lv_Pv_eq (hH : HostHyp d) (u : d.what₂.Word) (v : d.Pr.vT u) : (atTTied a hH u).Pv v = v.1.asIdeal := by
  first
    | rfl
    | exact Ideal.mk_ker
    | (show RingHom.ker (Ideal.Quotient.mk v.1.asIdeal) = v.1.asIdeal; exact Ideal.mk_ker)

set_option maxHeartbeats 1000000 in

def levelAgreement (hS : SpStd d.toColBase) (hH : HostHyp d) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) :
    CF.LvTied (D := d.colRec a) u (atTTied a hH u) i hi where
  pr := fun v c => tiePr d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c
  pr_surj := fun v c => tiePr_surj d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c
  pr_smul := fun v c r z => tiePr_smul d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c r z
  pr_ker := fun v c z => tiePr_ker d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c _ (lv_Pv_eq a hH u v) z
  fv_ker := fun v c z => tie_fv_ker d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c _ (lv_Pv_eq a hH u v) z
  prk := fun v c => tiePrk d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c _ (lv_Pv_eq a hH u v)
  prk_surj := fun v c => tiePrk_surj d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c _ (lv_Pv_eq a hH u v)
  prk_smul := fun v c r z =>
    tiePrk_smul d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c _ (lv_Pv_eq a hH u v) r z
  prk_ker := fun v c z => tiePrk_ker d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c _ (lv_Pv_eq a hH u v) z
  te := fun v c z hz h => tiePrk_te d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c _ (lv_Pv_eq a hH u v) z hz h

end Rec

end Formalism.L2.Col
