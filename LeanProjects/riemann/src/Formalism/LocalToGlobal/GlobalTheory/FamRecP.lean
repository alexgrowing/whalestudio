import Formalism.LocalToGlobal.GlobalTheory.FamRec

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

theorem prBelow_plF (D : D7) (w : D.what₂.places.Pl) :
    LChain2.prBelow (plF D w) = D.what₂.places.resChar w :=
  (LChain2.prBelow_iff (plF D w) _).2
    (J.liesOver_of_mem _ (D.what₂.places.resChar_prime w) (D.plEq w) (J.resChar_mem D w))

theorem prBelow_eq (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) :
    LChain2.prBelow z = D.what₂.places.resChar (plB D z) := by
  conv_lhs => rw [← plF_plB D z]
  exact prBelow_plF D _

theorem ramE_plF (D : D7) (w : D.what₂.places.Pl) :
    LChain2.ramE (plF D w) = (D.what₂.places.ramIdx w : ℝ) := by
  rw [D.ram_eq w]; rfl

theorem ramE_eq (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) :
    LChain2.ramE z = (D.what₂.places.ramIdx (plB D z) : ℝ) := by
  conv_lhs => rw [← plF_plB D z]
  exact ramE_plF D _

theorem ell_plF (D : D7) (w : D.what₂.places.Pl) : slopeLatticeData.ell (plF D w) = SizeData₂.lwP w := rfl

theorem lE_plF (D : D7) (w : D.what₂.places.Pl) :
    LChain2.lE (plF D w) = SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
  unfold LChain2.lE
  rw [ramE_plF, ell_plF]

theorem lE_eq (D : D7) (z : slopeLatticeData.FinPl D.what₂.LL) :
    LChain2.lE z = SizeData₂.lwP (plB D z) * (D.what₂.places.ramIdx (plB D z) : ℝ) := by
  conv_lhs => rw [← plF_plB D z]
  exact lE_plF D _

theorem plF_injective (D : D7) : Function.Injective (plF D) := fun a b h => by
  rw [← plB_plF D a, h, plB_plF]

variable {D : D7} (L : SizeData₂ D)

theorem prOf_prime {p : ℕ} (hp : p ∈ prOf L) : p.Prime := by
  unfold prOf at hp
  rcases Finset.mem_union.1 hp with h | h
  · obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 h
    exact D.what₂.places.resChar_prime w
  · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 h
    exact (D.mem u).A.T_prime

theorem mem_SOf (z : slopeLatticeData.FinPl D.what₂.LL) : z ∈ SOf L ↔ LChain2.prBelow z ∈ prOf L := by
  unfold SOf
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hz⟩
    rw [(LChain2.mem_plOver (prOf_prime L hp) z).1 hz]
    exact hp
  · intro h
    exact ⟨_, h, (LChain2.mem_plOver (prOf_prime L h) z).2 rfl⟩

theorem mem_SOf_plF (w : D.what₂.places.Pl) : plF D w ∈ SOf L ↔ D.what₂.places.resChar w ∈ prOf L := by
  rw [mem_SOf, prBelow_plF]

theorem plF_mem_of_supp {w : D.what₂.places.Pl} (hw : w ∈ L.supp) : plF D w ∈ SOf L :=
  (mem_SOf_plF L w).2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))

theorem place_mem_of_twist_prime {w : D.what₂.places.Pl} {u : D.what₂.Word} (hw : D.what₂.places.resChar w = (D.mem u).A.T) :
    plF D w ∈ SOf L :=
  (mem_SOf_plF L w).2 (Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, Finset.mem_univ _, hw.symm⟩))

theorem not_supp_of_not_mem {z : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∉ SOf L) : plB D z ∉ L.supp := fun h =>
  hz (by have := plF_mem_of_supp L h; rwa [plF_plB] at this)

theorem not_T_of_not_mem {z : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∉ SOf L) (u : D.what₂.Word) :
    D.what₂.places.resChar (plB D z) ≠ (D.mem u).A.T := fun h =>
  hz (by have := place_mem_of_twist_prime L h; rwa [plF_plB] at this)

theorem sum_SOf (g : D.what₂.places.Pl → ℝ) (hg : ∀ w, w ∉ L.supp → g w = 0) :
    ∑ z ∈ SOf L, g (plB D z) = ∑ w ∈ L.supp, g w := by
  classical
  have h1 : ∑ w ∈ L.supp, g w = ∑ z ∈ L.supp.image (plF D), g (plB D z) := by
    rw [Finset.sum_image (fun a _ b _ h => plF_injective D h)]
    exact Finset.sum_congr rfl (fun w _ => by rw [plB_plF])
  rw [h1]
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
    exact plF_mem_of_supp L hw
  · intro z _ hz
    apply hg
    intro h
    exact hz (Finset.mem_image.2 ⟨plB D z, h, plF_plB D z⟩)

theorem gainD_off (j : ℕ) {w : D.what₂.places.Pl} (hw : w ∉ L.supp) : L.gainD j w = 0 := by
  unfold SizeData₂.gainD
  split_ifs
  · rfl
  · exact L.gain_supp j w hw

theorem sg_off (u : D.what₂.Word) {w : D.what₂.places.Pl} (hw : w ∉ L.supp) : L.sg u w = 0 := by
  unfold SizeData₂.sg
  apply Finset.sum_eq_zero
  intro j _
  rw [gainD_off L j hw, L.F_supp j w hw, L.E_supp u j w hw]
  ring

theorem tauZ_apply (z : slopeLatticeData.FinPl D.what₂.LL) :
    tauZ L z = ⌊DV.ur D (plB D z) (L.tau (plB D z))⌋ := by
  show (if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.tau (plB D z))⌋ else 0) = _
  split_ifs with h
  · rfl
  · rw [L.tau_supp _ (not_supp_of_not_mem L h)]
    simp [DV.ur]

theorem sgZ_apply (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    sgZ L u z = ⌊DV.ur D (plB D z) (L.sg u (plB D z))⌋ := by
  show (if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.sg u (plB D z))⌋ else 0) = _
  split_ifs with h
  · rfl
  · rw [sg_off L u (not_supp_of_not_mem L h)]
    simp [DV.ur]

theorem ramIdx_pos' (w : D.what₂.places.Pl) : (0 : ℝ) < (D.what₂.places.ramIdx w : ℝ) := by
  exact_mod_cast D.what₂.places.ramIdx_pos w

theorem tauZ_nat (hτ : TauNat L) (z : slopeLatticeData.FinPl D.what₂.LL) :
    (tauZ L z : ℝ) = (D.what₂.places.ramIdx (plB D z) : ℝ) * L.tau (plB D z) := by
  obtain ⟨n, hn⟩ := hτ (plB D z)
  rw [tauZ_apply, hn]
  unfold DV.ur
  have : ((D.what₂.places.ramIdx (plB D z) : ℝ) * (n : ℝ)) = (((D.what₂.places.ramIdx (plB D z) * n : ℕ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [this, Int.floor_intCast]

theorem tauZ_nonneg (hτ : TauNat L) (z : slopeLatticeData.FinPl D.what₂.LL) : 0 ≤ tauZ L z := by
  obtain ⟨n, hn⟩ := hτ (plB D z)
  rw [tauZ_apply, hn]
  apply Int.floor_nonneg.2
  unfold DV.ur
  positivity

theorem ioPr_resChar (hio : IoPrime L) (w : D.what₂.places.Pl) : ioPr L (D.what₂.places.resChar w) = L.io w := by
  have hex : ∃ w' : D.what₂.places.Pl, D.what₂.places.resChar w' = D.what₂.places.resChar w := ⟨w, rfl⟩
  unfold ioPr
  rw [dif_pos hex]
  exact hio _ _ hex.choose_spec

section Proj
variable (m : ℕ) (A : Mx D)

theorem lenR_famOf (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    (famOf L m A).lenR u z = (fam0 L m A).lenR u z := rfl

theorem tauR_famOf (hτ : TauNat L) (z : slopeLatticeData.FinPl D.what₂.LL) : (famOf L m A).tauR z = L.tau (plB D z) := by
  show (tauZ L z : ℝ) / LChain2.ramE z = _
  rw [tauZ_nat L hτ, ramE_eq]
  field_simp [(ramIdx_pos' (plB D z)).ne']

end Proj

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.HN Formalism.LFunctionChainParameters Formalism.HN.DualPolygon

namespace Len

section Gen

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem locLen_tower (w : Ideal R) [w.IsPrime] (A B C : Submodule R V) (hCB : C ≤ B) (hBA : B ≤ A) :
    slopeLatticeData.locLen w (A ⧸ C.comap A.subtype) =
      slopeLatticeData.locLen w (B ⧸ C.comap B.subtype) + slopeLatticeData.locLen w (A ⧸ B.comap A.subtype) := by
  let f : (B ⧸ C.comap B.subtype) →ₗ[R] (A ⧸ C.comap A.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBA) (fun x hx => hx)
  let g : (A ⧸ C.comap A.subtype) →ₗ[R] (A ⧸ B.comap A.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hCB hx)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    intro h
    have h1 : (Submodule.inclusion hBA b) ∈ C.comap A.subtype := by
      have : Submodule.Quotient.mk (p := C.comap A.subtype) (Submodule.inclusion hBA b) = 0 := h
      exact (Submodule.Quotient.mk_eq_zero _).1 this
    exact (Submodule.Quotient.mk_eq_zero _).2 h1
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have H : Function.Exact f g := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
    constructor
    · intro h
      have h1 : a ∈ B.comap A.subtype := by
        have : Submodule.Quotient.mk (p := B.comap A.subtype) a = 0 := h
        exact (Submodule.Quotient.mk_eq_zero _).1 this
      exact ⟨Submodule.Quotient.mk ⟨a.1, h1⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← hx]
      have : Submodule.Quotient.mk (p := B.comap A.subtype) (Submodule.inclusion hBA b) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 b.2
      exact this
  exact slopeLatticeData.locLen_exact w f g hf hg H

theorem locLen_zero (w : Ideal R) [w.IsPrime] (A B : Submodule R V)
    (h : ∀ a ∈ A, ∃ s : R, s ∉ w ∧ s • a ∈ B) : slopeLatticeData.locLen w (A ⧸ B.comap A.subtype) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (A ⧸ B.comap A.subtype))).2 ?_)
  intro x
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨s, hs, hsa⟩ := h a.1 a.2
  refine ⟨s, hs, ?_⟩
  have : Submodule.Quotient.mk (p := B.comap A.subtype) (s • a) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hsa
  exact this

end Gen

section NF

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]

theorem lenAt_eq (w : slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V) :
    slopeLatticeData.lenAt w A B = (have := w.2.isPrime; slopeLatticeData.locLen w.1 (A ⧸ B.comap A.subtype)) := rfl

theorem lenAt_tower (w : slopeLatticeData.FinPl K) (A B C : Submodule (𝓞 K) V) (hCB : C ≤ B) (hBA : B ≤ A) :
    slopeLatticeData.lenAt w A C = slopeLatticeData.lenAt w B C + slopeLatticeData.lenAt w A B := by
  have := w.2.isPrime
  exact locLen_tower w.1 A B C hCB hBA

theorem lenAt_zero (w : slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V)
    (h : ∀ a ∈ A, ∃ s : 𝓞 K, s ∉ w.1 ∧ s • a ∈ B) : slopeLatticeData.lenAt w A B = 0 := by
  have := w.2.isPrime
  exact locLen_zero w.1 A B h

theorem index_smul (X : Submodule (𝓞 K) V) (hX : X.FG) (𝔟 : Ideal (𝓞 K)) (h𝔟 : 𝔟 ≠ ⊥) :
    (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup =
      Ideal.absNorm 𝔟 ^ finrank K (Submodule.span K (X : Set V)) := by
  let _ : StarRing K := starRingOfComm
  set m := Ideal.absNorm 𝔟 with hmdef
  have hm : m ≠ 0 := fun h => h𝔟 (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (m : 𝓞 K) ∈ 𝔟 := Ideal.absNorm_mem 𝔟
  obtain ⟨𝔠, h𝔠⟩ : 𝔟 ∣ Ideal.span {(m : 𝓞 K)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have hspan0 : Ideal.span {(m : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm
  have h𝔠0 : 𝔠 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h𝔠
    exact hspan0 h𝔠
  set r := finrank K (Submodule.span K (X : Set V)) with hr
  have hall := twist_int X hX m hm
  rw [twist_finrank_int X hX, h𝔠, mul_comm, Submodule.mul_smul,
    ← AddSubgroup.relIndex_mul_relIndex (𝔠 • 𝔟 • X).toAddSubgroup
      (𝔟 • X).toAddSubgroup X.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)
      ((Submodule.toAddSubgroup_le _ _).2 Submodule.smul_le_right)] at hall
  have ha := twist_le 𝔟 h𝔟 X hX
  have hb := twist_le 𝔠 h𝔠0 (𝔟 • X) (Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hX)
  rw [twist_span_smul X 𝔟 h𝔟] at hb
  have hnorm : Ideal.absNorm 𝔠 * m = m ^ finrank ℚ K := by
    rw [hmdef, ← map_mul, mul_comm, ← h𝔠, twist_absNorm_nat]
  have hB : 0 < Ideal.absNorm 𝔠 ^ r :=
    pow_pos (Nat.pos_of_ne_zero (fun h => h𝔠0 (Ideal.absNorm_eq_zero_iff.1 h))) _
  have htot : Ideal.absNorm 𝔠 ^ r * m ^ r = m ^ (finrank ℚ K * r) := by
    rw [← mul_pow, hnorm, ← pow_mul]
  by_contra hne
  have hlt := lt_of_le_of_ne ha hne
  have h1 : (𝔠 • 𝔟 • X).toAddSubgroup.relIndex (𝔟 • X).toAddSubgroup *
      (𝔟 • X).toAddSubgroup.relIndex X.toAddSubgroup < Ideal.absNorm 𝔠 ^ r * m ^ r :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hb) (Nat.mul_lt_mul_of_pos_left hlt hB)
  rw [hall, htot] at h1
  exact lt_irrefl _ h1

def Good (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] (w : slopeLatticeData.FinPl K) (J : Ideal (𝓞 K)) (c : ℕ) : Prop :=
  J ≠ ⊥ ∧ ∀ Y : Submodule (𝓞 K) V, Y.FG → Submodule.span K (Y : Set V) = ⊤ →
    slopeLatticeData.lenAt w Y (J • Y) = ((finrank K V * c : ℕ) : ℕ∞)

theorem good_one (w : slopeLatticeData.FinPl K) : Good V w 1 0 := by
  refine ⟨one_ne_zero, fun Y _ _ => ?_⟩
  rw [Submodule.one_smul, mul_zero, Nat.cast_zero]
  exact lenAt_zero w Y Y (fun a ha => ⟨1, fun h => w.2.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩)

theorem good_mul (w : slopeLatticeData.FinPl K) {J J' : Ideal (𝓞 K)} {c c' : ℕ} (h : Good V w J c) (h' : Good V w J' c') :
    Good V w (J * J') (c + c') := by
  refine ⟨mul_ne_zero h.1 h'.1, fun Y hY hsp => ?_⟩
  rw [Submodule.mul_smul, lenAt_tower w Y (J' • Y) (J • J' • Y) Submodule.smul_le_right Submodule.smul_le_right,
    h'.2 Y hY hsp, h.2 (J' • Y) (Submodule.FG.smul (IsNoetherian.noetherian J') hY)
      (by rw [twist_span_smul Y J' h'.1, hsp])]
  push_cast
  ring

theorem good_ne (w a : slopeLatticeData.FinPl K) (h : a ≠ w) : Good V w a.1 0 := by
  refine ⟨slopeLatticeData.finPl_ne_bot a, fun Y _ _ => ?_⟩
  rw [mul_zero, Nat.cast_zero]
  have hnle : ¬ a.1 ≤ w.1 := fun hle => h (Subtype.ext (a.2.eq_of_le w.2.ne_top hle))
  obtain ⟨s, hsa, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  exact lenAt_zero w Y _ (fun y hy => ⟨s, hsw, Submodule.smul_mem_smul hsa hy⟩)

theorem good_self (w : slopeLatticeData.FinPl K) : Good V w w.1 1 := by
  classical
  refine ⟨slopeLatticeData.finPl_ne_bot w, fun Y hY hsp => ?_⟩
  have hidx := index_smul Y hY w.1 (slopeLatticeData.finPl_ne_bot w)
  rw [hsp, finrank_top] at hidx
  have hN0 : Ideal.absNorm w.1 ≠ 0 := fun h => slopeLatticeData.finPl_ne_bot w (Ideal.absNorm_eq_zero_iff.1 h)
  have hN1 : Ideal.absNorm w.1 ≠ 1 := fun h => w.2.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have hne : (w.1 • Y).toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 := by
    rw [hidx]; exact pow_ne_zero _ hN0
  obtain ⟨k, hk, hc⟩ := slopeLatticeData.index_finsupp Y (w.1 • Y) hne
  have hk0 : ∀ w' : slopeLatticeData.FinPl K, w' ≠ w → k w' = 0 := by
    intro w' hw'
    have h1 := (good_ne (V := V) w' w (fun h => hw' h.symm)).2 Y hY hsp
    rw [hk w', mul_zero] at h1
    exact_mod_cast h1
  have hsub : k.support ⊆ {w} := by
    intro w' hw'
    rw [Finset.mem_singleton]
    by_contra hcon
    exact (Finsupp.mem_support_iff.1 hw') (hk0 w' hcon)
  rw [Finsupp.prod_of_support_subset k hsub _ (fun _ _ => pow_zero _), Finset.prod_singleton, hidx] at hc
  have h2 : 2 ≤ Ideal.absNorm w.1 := by omega
  have := Nat.pow_right_injective h2 hc
  rw [hk w, mul_one, this]

theorem good_pow (w a : slopeLatticeData.FinPl K) (k : ℕ) : Good V w (a.1 ^ k) (if a = w then k else 0) := by
  induction k with
  | zero => simpa using good_one (V := V) w
  | succ k ih =>
    rw [pow_succ]
    by_cases h : a = w
    · subst h
      have := good_mul a ih (good_self (V := V) a)
      simpa using this
    · have := good_mul w ih (good_ne (V := V) w a h)
      simpa [h] using this

theorem good_prod (w : slopeLatticeData.FinPl K) (n : slopeLatticeData.FinPl K → ℕ) (s : Finset (slopeLatticeData.FinPl K)) :
    Good V w (∏ a ∈ s, a.1 ^ n a) (∑ a ∈ s, if a = w then n a else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one (V := V) w
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact good_mul w (good_pow w a (n a)) ih

theorem idealPow_eq (τ : slopeLatticeData.FinPl K →₀ ℤ) (hτ : ∀ w, 0 ≤ τ w) :
    slopeLatticeData.idealPow τ = ((∏ a ∈ τ.support, a.1 ^ (τ a).toNat : Ideal (𝓞 K)) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  unfold slopeLatticeData.idealPow Finsupp.prod
  rw [← FractionalIdeal.coeIdealHom_apply, map_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [map_pow, FractionalIdeal.coeIdealHom_apply, ← zpow_natCast, Int.toNat_of_nonneg (hτ a)]

end NF

end Len

theorem length_twist : LenTwist := by
  classical
  intro K V _ _ _ _ _ _ _ τ M N hτ hM hsp hN w
  rw [Len.idealPow_eq τ hτ, slopeLatticeData.idealSmul_coeIdeal] at hN ⊢
  have hg := Len.good_prod (V := V) w (fun a => (τ a).toNat) τ.support
  rw [Len.lenAt_tower w M _ N hN Submodule.smul_le_right, hg.2 M hM hsp]
  congr 3
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.notMem_support_iff.1 h]; rfl

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

theorem card_lattice_level_zero : CardLat0 := by
  intro D u
  have h := (D.fm u).emb_basis 0
  have h1 := finrank_span_eq_card h.1
  rw [h.2, (D.fm u).Fi_zero] at h1
  exact h1.symm

theorem idealPow_sgZ {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) :
    slopeLatticeData.idealPow (-(sgZ L u)) = DV.Iu D L u := by
  classical
  unfold slopeLatticeData.idealPow DV.Iu
  rw [Finsupp.prod_of_support_subset (s := L.supp.image (plF D))]
  · rw [Finset.prod_image (fun a _ b _ h => plF_injective D h)]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [Finsupp.neg_apply, sgZ_apply, plB_plF]
    rfl
  · intro z hz
    rw [Finsupp.mem_support_iff, Finsupp.neg_apply, sgZ_apply] at hz
    refine Finset.mem_image.2 ⟨plB D z, ?_, plF_plB D z⟩
    by_contra hn
    apply hz
    rw [sg_off L u hn]
    simp [DV.ur]
  · intro z _
    exact zpow_zero _

theorem lattice_N_prime_eq : NprimeEq := by
  intro D L m A hdef u
  rw [hdef u]
  show slopeLatticeData.modLat (sgZ L u) (L.NuLat u) = _
  unfold slopeLatticeData.modLat HermitianLatticesTheory.idealSmul
  rw [idealPow_sgZ]
  rfl

theorem card_RR (D : D7) : Fintype.card D.div.RR.ι = D.what₂.Drows := by
  rw [← Module.finrank_eq_card_basis D.div.RR.b, D.RRV_finrank]

theorem card_all (D : D7) (h : 0 < D.what₂.Dall) :
    Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) = D.what₂.Dall := by
  have hle := D.Drows_le_Dall h
  rw [Fintype.card_sum, Fintype.card_fin, card_RR]
  omega

theorem del_famOf_rr {D : D7} (L : SizeData₂ D) (m : ℕ) (A : Mx D) (h : 0 < D.what₂.Dall) :
    (famOf L m A).del = D.what₂.delp := by
  have hR : (0 : ℝ) < (D.what₂.Dall : ℝ) := by exact_mod_cast h
  show 1 - (Fintype.card D.div.RR.ι : ℝ) /
    (Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) : ℝ) = _
  rw [card_all D h, card_RR, D.what₂.D_eq]
  field_simp
  ring

theorem rank_eq_card_rr {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (h : Submodule.span K (A.L : Set A.V) = ⊤) : A.rank = Fintype.card A.ι := by
  unfold HLat.rank Formalism.HN.rkK
  rw [h, finrank_top, Module.finrank_eq_card_basis A.b]

theorem lattice_hypotheses_small : LatticeHypothesisOfColumnFacts := by
  intro D L m A sg hdef hRR hNu hrk hOne hht hDall hd1 hM hall hsg0 hsg20 hRs h0 h0' h1 he0 hse
  have hd0 : 0 ≤ D.what₂.delp := D.delpNonneg hDall
  obtain ⟨mY, mY', mblock, mγ, mBV, mV, mk1, mk2⟩ := hM
  have hN : (famOf L m A).N' = fun u => (D.div.Nu u).L := funext (lattice_N_prime_eq D L m A hdef)
  have hdel := del_famOf_rr L m A hDall
  have hD0 : 0 < D.what₂.Dstar := by rw [← D.Dstar_eq D.u₀]; exact (D.mem D.u₀).A.Dstar_pos
  have hsum : 0 < ∑ u, Fintype.card (D.div.Nu u).ι :=
    Finset.sum_pos (fun u _ => by rw [← rank_eq_card_rr (D.div.Nu u) (hNu u).2]; exact hrk u) Finset.univ_nonempty
  have : FiniteDimensional D.what₂.LL D.div.RR.V := Module.Finite.of_basis D.div.RR.b
  unfold LChain2.Fam.LatHyp
  rw [hN, hdel]
  refine ⟨⟨Formalism.HN.DualPolygon.dualFrame_unit D.div.RR.X D.div_good.1, D.div_good.2, mY, mY',
    Formalism.HN.DualPolygon.dualLat_fg D.div.RR.L hRR.2, Formalism.HN.DualPolygon.dualLat_span D.div.RR.L hRR.1 hRR.2,
    fun u => (hNu u).1, fun u => (hNu u).2, hsum, hOne, hht, hd0, hd1, ?_, mblock⟩, mγ, mBV, mV, hD0, hsg0, hsg20, ?_,
    h0, h0', h1, he0, hse, ?_, ?_, ?_⟩
  · show (1 - D.what₂.delp) * (Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) : ℝ) ≤
      (Fintype.card D.div.RR.ι : ℝ)
    rw [card_all D hDall, card_RR, D.what₂.D_eq]
  · have hc : MatrixLatticeEstimates.RsG (famOf L m A).ιf = ∑ u, (D.duS u : ℝ) := by
      unfold MatrixLatticeEstimates.RsG
      refine Finset.sum_congr rfl (fun u _ => ?_)
      exact_mod_cast card_lattice_level_zero D u
    rw [hc]
    exact hRs
  · intro u u' huu
    have hc : ∀ u, (Fintype.card ((famOf L m A).ιf u) : ℝ) = (D.duS u : ℝ) := fun u => by
      exact_mod_cast card_lattice_level_zero D u
    rw [hc u, hc u']
    exact mk1 u u' huu
  · intro u
    have hc : (Fintype.card ((famOf L m A).ιf u) : ℝ) = (D.duS u : ℝ) := by
      exact_mod_cast card_lattice_level_zero D u
    rw [hc]
    exact mk2 u
  · show (Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) : ℝ) ≤ (1 + A.η1) * D.what₂.Dstar
    rw [card_all D hDall]
    exact hall

theorem hsSq_submatrix {m n m' n' : Type} [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] (M : Matrix m n ℂ)
    (e : m' ≃ m) (e' : n' ≃ n) : HilbertSchmidtNormSquare.hsSq (M.submatrix e e') = HilbertSchmidtNormSquare.hsSq M := by
  unfold HilbertSchmidtNormSquare.hsSq
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Equiv.sum_comp e']
  rfl

theorem matRec_of_fin (D : D7) (η0 η1 e0 : ℝ) (v : InfinitePlace D.what₂.LL)
    (Y : ∀ u, Matrix (D.div.Nu u).ι (D.div.Nu u).ι ℂ) (Y' : Matrix D.div.RR.ι D.div.RR.ι ℂ)
    (Ball : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (D.div.Nu u).ι ℂ) (γ : D.what₂.Word → ℝ)
    (Bf : ∀ u, Matrix (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) (Fin (D.duS u)) ℂ)
    (Vr : ∀ u, Matrix (Fin (D.duS u)) (D.div.Nu u).ι ℂ)
    (h : (∀ u, IsUnit (Y u).det) ∧ IsUnit Y'.det ∧
      (∀ u (k : D.div.RR.ι) (j : (D.div.Nu u).ι), Ball u (Sum.inl k) j =
        (Y'⁻¹ * (LinearMap.toMatrix (D.div.Nu u).b D.div.RR.dualB (D.div.Bk u)).map v.embedding * Y u) k j) ∧
      (∀ u, 0 < γ u) ∧ (∀ u, Ball u = Bf u * Vr u) ∧ (∀ u, (Vr u)ᴴ * Vr u = 1) ∧
      (∀ u u', u ≠ u' → HilbertSchmidtNormSquare.hsSq (MatrixLatticeEstimates.KpG Bf γ u u') ≤
        (1 + η0) * (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar) ∧
      (∀ u, HilbertSchmidtNormSquare.hsSq (MatrixLatticeEstimates.KdG Bf γ u - 1) ≤ e0 * (D.duS u : ℝ))) :
    ∃ A : Mx D, A.η0 = η0 ∧ A.η1 = η1 ∧ A.e0 = e0 ∧ MatRec A := by
  obtain ⟨m1, m2, m3, m4, m5, m6, k1, k2⟩ := h
  let e : ∀ u, ((D.fm u).lat 0).ι ≃ Fin (D.duS u) := fun u => Fintype.equivFinOfCardEq (card_lattice_level_zero D u)
  have hK : ∀ u u', MatrixLatticeEstimates.KpG (fun u => (Bf u).submatrix id (e u)) γ u u' =
      (MatrixLatticeEstimates.KpG Bf γ u u').submatrix (e u) (e u') := by
    intro u u'
    ext i j
    simp only [MatrixLatticeEstimates.KpG, Matrix.smul_apply, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, id]
  refine ⟨⟨v, Y, Y', Ball, γ, fun u => (Bf u).submatrix id (e u), fun u => (Vr u).submatrix (e u) id, η0, η1, e0⟩,
    rfl, rfl, rfl, m1, m2, m3, m4, ?_, ?_, ?_, ?_⟩
  · intro u
    show Ball u = (Bf u).submatrix id (e u) * (Vr u).submatrix (e u) id
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    exact m5 u
  · intro u
    show ((Vr u).submatrix (e u) id)ᴴ * (Vr u).submatrix (e u) id = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
    exact m6 u
  · intro u u' huu
    show HilbertSchmidtNormSquare.hsSq (MatrixLatticeEstimates.KpG (fun u => (Bf u).submatrix id (e u)) γ u u') ≤ _
    rw [hK, hsSq_submatrix]
    exact k1 u u' huu
  · intro u
    show HilbertSchmidtNormSquare.hsSq (MatrixLatticeEstimates.KdG (fun u => (Bf u).submatrix id (e u)) γ u - 1) ≤ _
    have h1 : MatrixLatticeEstimates.KdG (fun u => (Bf u).submatrix id (e u)) γ u - 1 = (MatrixLatticeEstimates.KdG Bf γ u - 1).submatrix (e u) (e u) := by
      unfold MatrixLatticeEstimates.KdG
      rw [hK u u]
      ext i j
      simp [Matrix.sub_apply, Matrix.one_apply, (e u).injective.eq_iff]
    rw [h1, hsSq_submatrix]
    exact k2 u

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

section Alg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem mem_of_loc (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ w : slopeLatticeData.FinPl K, ∃ s : 𝓞 K, s ∉ w.1 ∧ s • x ∈ M) : x ∈ M := by
  let I : Ideal (𝓞 K) := M.comap (LinearMap.toSpanSingleton (𝓞 K) V x)
  have hI : ∀ a : 𝓞 K, a ∈ I ↔ a • x ∈ M := fun a => Iff.rfl
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨s, hs, hsx⟩ := h ⟨m, hm⟩
    exact hs (hle ((hI s).2 hsx))
  have h2 := (hI 1).1 (by rw [htop]; trivial)
  rwa [one_smul] at h2

theorem int_smul' (d : 𝓞 K) (v : V) : d • v = (algebraMap (𝓞 K) K d) • v := (algebraMap_smul K d v).symm

theorem algMap_ne' {d : 𝓞 K} (hd : d ≠ 0) : algebraMap (𝓞 K) K d ≠ 0 := by
  intro h
  exact hd ((injective_iff_map_eq_zero (algebraMap (𝓞 K) K)).mp (IsFractionRing.injective (𝓞 K) K) d h)

theorem exists_mul_mem' (L : Submodule (𝓞 K) V) (v : V) (hv : v ∈ Submodule.span K (L : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨d1, h1, m1⟩ := hx
    obtain ⟨d2, h2, m2⟩ := hy
    refine ⟨d1 * d2, mul_ne_zero h1 h2, ?_⟩
    have e : (d1 * d2) • (x + y) = d2 • (d1 • x) + d1 • (d2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm d2 d1]
    rw [e]
    exact L.add_mem (L.smul_mem _ m1) (L.smul_mem _ m2)
  | smul a x _ hx =>
    obtain ⟨d, h1, m1⟩ := hx
    obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
    refine ⟨m * d, mul_ne_zero hm0 h1, ?_⟩
    have e : (m * d) • ((algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K m) • x) = n • (d • x) := by
      rw [int_smul' (m * d), int_smul' n, int_smul' d, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp [algMap_ne' hm0]
    rw [e]
    exact L.smul_mem _ m1

theorem span_eq_of_commens {M N : Submodule (𝓞 K) V} (hNM : N ≤ M) {c : 𝓞 K} (hc : c ≠ 0)
    (hcM : ∀ y ∈ M, c • y ∈ N) : Submodule.span K (N : Set V) = Submodule.span K (M : Set V) := by
  apply le_antisymm (Submodule.span_mono hNM)
  refine Submodule.span_le.2 (fun y hy => ?_)
  have h1 : c • y ∈ Submodule.span K (N : Set V) := Submodule.subset_span (hcM y hy)
  have h2 : y = (algebraMap (𝓞 K) K c)⁻¹ • (c • y) := by
    rw [int_smul' c y, smul_smul, inv_mul_cancel₀ (algMap_ne' hc), one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ h1

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem lenAt_eq_zero (w : slopeLatticeData.FinPl K) (A B : Submodule (𝓞 K) V)
    (h : ∀ y ∈ A, ∃ s : 𝓞 K, s ∉ w.1 ∧ s • y ∈ B) : slopeLatticeData.lenAt w A B = 0 := by
  have := w.2.isPrime
  unfold slopeLatticeData.lenAt
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.1.primeCompl
    (LocalizedModule.mkLinearMap w.1.primeCompl (A ⧸ B.comap A.subtype))).2 ?_)
  intro q
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨s, hs, hsy⟩ := h y.1 y.2
  refine ⟨s, hs, ?_⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show (s • y : A).1 ∈ B
  exact hsy

theorem idealPow_le_one (τ : slopeLatticeData.FinPl K →₀ ℤ) (hτ : ∀ w, 0 ≤ τ w) : slopeLatticeData.idealPow τ ≤ 1 := by
  unfold slopeLatticeData.idealPow Finsupp.prod
  refine Finset.prod_induction _ (fun J => J ≤ (1 : FI)) (fun a b ha hb => ?_) le_rfl (fun w _ => ?_)
  · calc a * b ≤ 1 * 1 := mul_le_mul' ha hb
      _ = 1 := one_mul 1
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hτ w)
    show ((w.1 : FI)) ^ τ w ≤ 1
    rw [hn, zpow_natCast]
    exact pow_le_one' FractionalIdeal.coeIdeal_le_one n

omit [IsScalarTower (𝓞 K) K V] in
theorem idealSmul_mono_left {I J : Submodule (𝓞 K) K} (h : I ≤ J) (L : Submodule (𝓞 K) V) :
    HermitianLatticesTheory.idealSmul I L ≤ HermitianLatticesTheory.idealSmul J L := by
  refine Submodule.span_mono ?_
  rintro z ⟨a, ha, x, hx, rfl⟩
  exact ⟨a, h ha, x, hx, rfl⟩

theorem idealSmul_le_self (τ : slopeLatticeData.FinPl K →₀ ℤ) (hτ : ∀ w, 0 ≤ τ w) (M : Submodule (𝓞 K) V) :
    HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow τ : FI) : Submodule (𝓞 K) K) M ≤ M := by
  have h := idealSmul_mono_left (FractionalIdeal.coe_le_coe.2 (idealPow_le_one τ hτ)) M
  rw [FractionalIdeal.coe_one, slopeLatticeData.idealSmul_one] at h
  exact h

theorem wUnit_erase (w : slopeLatticeData.FinPl K) (τ : slopeLatticeData.FinPl K →₀ ℤ) : slopeLatticeData.WUnit w.1 (slopeLatticeData.idealPow (τ.erase w)) := by
  have := w.2.isPrime
  unfold slopeLatticeData.idealPow Finsupp.prod
  refine Finset.prod_induction _ (fun J => slopeLatticeData.WUnit w.1 J) (fun a b ha hb => slopeLatticeData.wUnit_mul w.1 ha hb)
    (slopeLatticeData.wUnit_one w.1) (fun w' hw' => ?_)
  have hne : w' ≠ w := by
    intro h
    rw [h, Finsupp.mem_support_iff, Finsupp.erase_same] at hw'
    exact hw' rfl
  exact slopeLatticeData.wUnit_zpow w.1 (slopeLatticeData.wUnit_other w w' hne) _

theorem idealPow_split (w : slopeLatticeData.FinPl K) (τ : slopeLatticeData.FinPl K →₀ ℤ) :
    slopeLatticeData.idealPow τ = (w.1 : FI) ^ (τ w) * slopeLatticeData.idealPow (τ.erase w) := by
  conv_lhs => rw [← Finsupp.single_add_erase w τ]
  rw [slopeLatticeData.idealPow_add]
  congr 1
  unfold slopeLatticeData.idealPow
  exact Finsupp.prod_single_index (zpow_zero _)

theorem mem_idealSmul_of_loc (τ : slopeLatticeData.FinPl K →₀ ℤ) (hτ : ∀ w, 0 ≤ τ w) (M : Submodule (𝓞 K) V) (x : V)
    (h : ∀ w : slopeLatticeData.FinPl K, ∃ s : 𝓞 K, s ∉ w.1 ∧ s • x ∈ (w.1 ^ (τ w).toNat) • M) :
    x ∈ HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow τ : FI) : Submodule (𝓞 K) K) M := by
  refine mem_of_loc _ x (fun w => ?_)
  have := w.2.isPrime
  obtain ⟨s, hs, hsx⟩ := h w
  obtain ⟨-, -, t, ht, htJ⟩ := wUnit_erase w τ
  have hJ0 : slopeLatticeData.idealPow (τ.erase w) ≠ 0 := slopeLatticeData.idealPow_ne_zero _

  have htmem : algebraMap (𝓞 K) K t ∈ slopeLatticeData.idealPow (τ.erase w) := by
    have : algebraMap (𝓞 K) K t ∈ (slopeLatticeData.idealPow (τ.erase w))⁻¹⁻¹ := by
      rw [FractionalIdeal.mem_inv_iff (inv_ne_zero hJ0)]
      intro y hy
      obtain ⟨z, hz⟩ := htJ y hy
      rw [← hz]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨z, rfl⟩
    rwa [inv_inv] at this
  refine ⟨t * s, fun hts => (w.2.isPrime.mem_or_mem hts).elim ht hs, ?_⟩
  rw [mul_smul, int_smul' t]
  have hsx' : s • x ∈ HermitianLatticesTheory.idealSmul (((w.1 ^ (τ w).toNat : Ideal (𝓞 K)) : FI) : Submodule (𝓞 K) K) M := by
    rw [slopeLatticeData.idealSmul_coeIdeal]; exact hsx
  refine slopeLatticeData.smul_mem_idealSmul _ (fun c hc => ?_) hsx'
  rw [idealPow_split w τ]
  have hc' : c ∈ ((w.1 : FI) ^ (τ w)) := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (hτ w)
    rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
    rw [hn, Int.toNat_natCast] at hc
    exact hc
  rw [mul_comm (algebraMap (𝓞 K) K t) c]
  exact FractionalIdeal.mul_mem_mul hc' htmem

end Alg

section Rec

variable {D : D7} (L : SizeData₂ D) (m : ℕ) (A : Mx D)

def itD (u : D.what₂.Word) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  HermitianLatticesTheory.idealSmul ((slopeLatticeData.idealPow (tauZ L) : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) :
    Submodule (𝓞 D.what₂.LL) D.what₂.LL) (DV.MramL D u)

theorem card_lattice_zero_eq_dual_size (u : D.what₂.Word) : Fintype.card ((D.fm u).lat 0).ι = D.duS u := by
  unfold D7.duS
  rw [← (D.fm u).Fi_zero, ← ((D.fm u).emb_basis 0).2, finrank_span_eq_card ((D.fm u).emb_basis 0).1]

theorem card_nu (u : D.what₂.Word) : Fintype.card (D.div.Nu u).ι = (D.mem u).A.du := by
  rw [← Module.finrank_eq_card_basis (D.div.Nu u).b]
  exact D.NuV_finrank u

theorem span_MramL (u : D.what₂.Word) :
    Submodule.span D.what₂.LL (DV.MramL D u : Set (D.div.Nu u).V) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : D.nuIn u x ∈ Submodule.span D.what₂.LL (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
    rw [((D.fm u).lat_good 0).2.2]; trivial
  obtain ⟨d, hd, hdx⟩ := exists_mul_mem' _ _ hx
  have hmem : d • x ∈ DV.MramL D u := by
    show (D.nuIn u).restrictScalars (𝓞 D.what₂.LL) (d • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hdx
  have h2 : x = (algebraMap (𝓞 D.what₂.LL) D.what₂.LL d)⁻¹ • (d • x) := by
    rw [int_smul' d x, smul_smul, inv_mul_cancel₀ (algMap_ne' hd), one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem locLe_zero' {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    {w : HeightOneSpectrum (𝓞 K)} {A B : Submodule (𝓞 K) V} (h : DV.LocLe w 0 A B) :
    ∀ x ∈ A, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ B := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := h x hx
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hsx
  exact ⟨s, hs, hsx⟩

theorem exists_pl_over (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ z : slopeLatticeData.FinPl K, LChain2.prBelow z = p := by
  by_contra h
  push Not at h
  have h1 := LChain2.sum_log_norm_over_prime (∅ : Finset (slopeLatticeData.FinPl K)) p hp (fun w hw => absurd hw (h w))
  simp only [Finset.filter_empty, Finset.sum_empty] at h1
  have := Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < (p : ℝ))
  linarith

theorem itD_le (hτ : TauNat L) (u : D.what₂.Word) : itD L u ≤ DV.MramL D u :=
  idealSmul_le_self _ (tauZ_nonneg L hτ) _

theorem lattice_le_iterated_dual (hτ : TauNat L) (hAtT : AtT L)
    (hg1 : ∀ u w, D.what₂.places.resChar w ≠ (D.mem u).A.T →
      DV.LocLe (D.plEq w) ⌊DV.ur D w (L.tau w)⌋₊ (L.NuLat u) (DV.MramL D u) ∧
      (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * (L.tau w + L.io w))
    (htT : ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → L.tau w = 0) (u : D.what₂.Word) :
    L.NuLat u ≤ itD L u := by
  intro x hx
  refine mem_idealSmul_of_loc (tauZ L) (tauZ_nonneg L hτ) _ x (fun z => ?_)
  obtain ⟨w, rfl⟩ : ∃ w, z = plF D w := ⟨plB D z, (plF_plB D z).symm⟩
  by_cases hT : D.what₂.places.resChar w = (D.mem u).A.T
  · obtain ⟨s, hs, hsx⟩ := hAtT u w hT x hx
    have h0 : (tauZ L (plF D w)).toNat = 0 := by
      rw [tauZ_apply, plB_plF, htT u w hT]; simp [DV.ur]
    exact ⟨s, hs, by rw [h0]; exact hsx⟩
  · obtain ⟨s, hs, hsx⟩ := (hg1 u w hT).1 x hx
    have h0 : (tauZ L (plF D w)).toNat = ⌊DV.ur D w (L.tau w)⌋₊ := by
      rw [tauZ_apply, plB_plF]; exact Int.floor_toNat _
    exact ⟨s, hs, by rw [h0]; exact hsx⟩

theorem rk_eq_of_commens (hτ : TauNat L) (hC : Commens L) (hNI : ∀ u, L.NuLat u ≤ itD L u) (u : D.what₂.Word) :
    rkK (L.NuLat u) = rkK (DV.MramL D u) := by
  obtain ⟨c, hc, hcM⟩ := (hC u).2
  unfold rkK
  rw [span_eq_of_commens (le_trans (hNI u) (itD_le L hτ u)) hc hcM]

theorem lenEq_of (hLT : LenTwist) : LenEq := by
  intro D L m A hNu hC hτ hNI' u w
  have hNI : ∀ u, L.NuLat u ≤ itD L u := hNI'
  have hτ0 := tauZ_nonneg L hτ
  have hNM : L.NuLat u ≤ DV.MramL D u := le_trans (hNI u) (itD_le L hτ u)
  have hrk := rk_eq_of_commens L hτ hC hNI u
  have hri := slopeLatticeData.relIndex_ne_zero (D.div.Nu u).b (D.div.Nu u).X (D.div_good.2 u) (D.MramL_fg u) hNM hrk
  obtain ⟨k, hk, -⟩ := slopeLatticeData.index_finsupp _ _ hri
  have : FiniteDimensional D.what₂.LL (D.div.Nu u).V := Module.Finite.of_basis (D.div.Nu u).b
  have htw := hLT D.what₂.LL (D.div.Nu u).V (tauZ L) (DV.MramL D u) (L.NuLat u) hτ0 (D.MramL_fg u)
    (span_MramL u) (hNI u) (plF D w)
  have h3 := hNu.2.2 u w (k (plF D w)) (hk (plF D w))
  rw [hk (plF D w)] at htw
  have htw' : ((k (plF D w) : ℕ) : ℕ∞) = slopeLatticeData.lenAt (plF D w) (itD L u) (L.NuLat u) +
      ((finrank D.what₂.LL (D.div.Nu u).V * (tauZ L (plF D w)).toNat : ℕ) : ℕ∞) := htw
  clear htw
  set a := slopeLatticeData.lenAt (plF D w) (itD L u) (L.NuLat u) with ha
  have hatop : a ≠ ⊤ := by
    intro h; rw [h, top_add] at htw'; exact ENat.natCast_ne_top _ htw'
  have hanat : (a.toNat : ℕ∞) = a := ENat.natCast_toNat hatop
  have hsum : k (plF D w) = a.toNat + finrank D.what₂.LL (D.div.Nu u).V * (tauZ L (plF D w)).toNat := by
    have := htw'
    rw [← hanat] at this
    exact_mod_cast this
  have htau : ((tauZ L (plF D w) : ℤ) : ℝ) = ((tauZ L (plF D w)).toNat : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (hτ0 (plF D w))).symm
  have hcard : (Fintype.card (D.div.Nu u).ι : ℝ) = (finrank D.what₂.LL (D.div.Nu u).V : ℝ) := by
    rw [Module.finrank_eq_card_basis (D.div.Nu u).b]
  have he := ramIdx_pos' w
  show (((a.toNat : ℕ) : ℝ) + (Fintype.card (D.div.Nu u).ι : ℝ) * ((tauZ L (plF D w) : ℤ) : ℝ)) /
    LChain2.ramE (plF D w) = _
  rw [hcard, htau, ramE_plF]
  have h4 : ((a.toNat : ℝ) + (finrank D.what₂.LL (D.div.Nu u).V : ℝ) * ((tauZ L (plF D w)).toNat : ℝ)) =
      (k (plF D w) : ℝ) := by rw [hsum]; push_cast; ring
  rw [h4, h3]
  field_simp

theorem ta_eq (hτ : TauNat L) :
    2 * ∑ z ∈ SOf L, LChain2.lE z * (((tauZ L z : ℤ) : ℝ) / LChain2.ramE z) =
      ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) := by
  have h1 : ∀ z ∈ SOf L, LChain2.lE z * (((tauZ L z : ℤ) : ℝ) / LChain2.ramE z) =
      SizeData₂.lwP (plB D z) * (D.what₂.places.ramIdx (plB D z) : ℝ) * L.tau (plB D z) := by
    intro z _
    rw [lE_eq, tauZ_nat L hτ, ramE_eq]
    field_simp [(ramIdx_pos' (plB D z)).ne']
  rw [Finset.sum_congr rfl h1,
    sum_SOf L (fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.tau w)
      (fun w hw => by simp [L.tau_supp w hw]), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  unfold SizeData₂.sz
  ring

theorem sgw_eq (hm : D.R.m = m) (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    (famOf L m A).sgw u z = L.sg u (plB D z) := by
  show ∑ j : Fin m, (L.gainD (j.val + 1) (plB D z) + L.F (j.val + 1) (plB D z) - L.E u (j.val + 1) (plB D z)) = _
  unfold SizeData₂.sg
  rw [Lnk.sum_lifts D m hm (fun j => L.gainD j (plB D z) + L.F j (plB D z) - L.E u j (plB D z))]

theorem tauZ_off {z : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∉ SOf L) : tauZ L z = 0 := by
  show (if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.tau (plB D z))⌋ else 0) = 0
  rw [if_neg hz]

theorem sgZ_off (u : D.what₂.Word) {z : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∉ SOf L) : sgZ L u z = 0 := by
  show (if z ∈ SOf L then ⌊DV.ur D (plB D z) (L.sg u (plB D z))⌋ else 0) = 0
  rw [if_neg hz]

theorem ioPr_nonneg (hio : IoPrime L) (hio0 : ∀ w, 0 ≤ L.io w) (z : slopeLatticeData.FinPl D.what₂.LL) :
    0 ≤ ioPr L (LChain2.prBelow z) := by
  rw [prBelow_eq, ioPr_resChar L hio]
  exact hio0 _

theorem sat {z : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∈ SOf L) (z' : slopeLatticeData.FinPl D.what₂.LL)
    (h : LChain2.prBelow z' = LChain2.prBelow z) : z' ∈ SOf L :=
  (mem_SOf L z').2 (h ▸ (mem_SOf L z).1 hz)

theorem lenN_off (hτ : TauNat L)
    (hoff : ∀ u w, w ∉ L.supp → (∀ u', D.what₂.places.resChar w ≠ (D.mem u').A.T) →
      DV.LocEq (D.plEq w) (L.NuLat u) (DV.MramL D u)) (u : D.what₂.Word) {z : slopeLatticeData.FinPl D.what₂.LL}
    (hz : z ∉ SOf L) : (slopeLatticeData.lenAt z (itD L u) (L.NuLat u)).toNat = 0 := by
  rw [lenAt_eq_zero z _ _ ?_]
  · rfl
  intro y hy
  have hyM : y ∈ DV.MramL D u := itD_le L hτ u hy
  obtain ⟨w, rfl⟩ : ∃ w, z = plF D w := ⟨plB D z, (plF_plB D z).symm⟩
  have hw1 := not_supp_of_not_mem L hz
  have hw2 := not_T_of_not_mem L hz
  rw [plB_plF] at hw1 hw2
  exact locLe_zero' (hoff u w hw1 hw2).2 y hyM

theorem T_mem (u : D.what₂.Word) : (D.mem u).A.T ∈ (SOf L).image LChain2.prBelow := by
  obtain ⟨z, hz⟩ := exists_pl_over D.what₂.LL _ (D.mem u).A.T_prime
  refine Finset.mem_image.2 ⟨z, (mem_SOf L z).2 ?_, hz⟩
  rw [hz]
  exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, Finset.mem_univ _, rfl⟩)

theorem tau_atT (htT : ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T → L.tau w = 0) (u : D.what₂.Word)
    {z : slopeLatticeData.FinPl D.what₂.LL} (hz : LChain2.prBelow z = (D.mem u).A.T) : tauZ L z = 0 := by
  obtain ⟨w, rfl⟩ : ∃ w, z = plF D w := ⟨plB D z, (plF_plB D z).symm⟩
  rw [prBelow_plF] at hz
  rw [tauZ_apply, plB_plF, htT u w hz]; simp [DV.ur]

theorem sign_weight_le (hm : D.R.m = m) (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    ((sgZ L u z : ℤ) : ℝ) / LChain2.ramE z ≤ (famOf L m A).sgw u z := by
  rw [sgw_eq L m A hm, sgZ_apply, ramE_eq, div_le_iff₀ (ramIdx_pos' _)]
  have := Int.floor_le (DV.ur D (plB D z) (L.sg u (plB D z)))
  unfold DV.ur at this ⊢
  linarith

theorem place_facts_of_twist_length (hLT : LenTwist) : PlaceHypothesisOfPlaceSizes := by
  intro D L m A hm hτ hio hio0 hNu hC hAtT hg1 hoff htT hRam hSl hdu hTa hsz
  have hτ0 := tauZ_nonneg L hτ
  have hNI : ∀ u, L.NuLat u ≤ itD L u := fun u => lattice_le_iterated_dual L hτ hAtT hg1 htT u
  have hLen := lenEq_of hLT D L m A hNu hC hτ hNI
  have hdM : ∀ u, (famOf L m A).dM u = (D.duS u : ℝ) := fun u => by
    show (Fintype.card ((D.fm u).lat 0).ι : ℝ) = _
    rw [card_lattice_zero_eq_dual_size]
  refine ⟨fun z _ => hτ0 z, fun z hz => tauZ_off L hz, fun z _ => ioPr_nonneg L hio hio0 z,
    fun z hz z' h => sat L hz z' h, le_of_eq_of_le (ta_eq L hτ) hTa, fun u => ?_⟩
  have hdM0 : (0 : ℝ) < (famOf L m A).dM u := by rw [hdM]; exact_mod_cast hdu u
  refine ⟨D.MramL_fg u, span_MramL u, ((D.fm u).lat_good 0).2.1, ((D.fm u).lat_good 0).2.2, hNI u,
    rk_eq_of_commens L hτ hC hNI u, fun z hz => ⟨sgZ_off L u hz, lenN_off L hτ hoff u hz⟩, (hsz u).1,
    T_mem L u, fun z hz => tau_atT L htT u (Finset.mem_filter.1 hz).2, ?_, fun z hz => ?_, fun z hz => ?_,
    ?_, fun z _ => sign_weight_le L m A hm u z, ?_, ?_, (hsz u).2⟩
  · show (Fintype.card (D.div.Nu u).ι : ℝ) = (famOf L m A).dM u * _
    rw [card_nu, hdM]
    exact hRam u
  · obtain ⟨w, rfl⟩ : ∃ w, z = plF D w := ⟨plB D z, (plF_plB D z).symm⟩
    have hT : D.what₂.places.resChar w ≠ (D.mem u).A.T := by
      intro h
      exact (Finset.mem_sdiff.1 hz).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hz).1, by
        show LChain2.prBelow (plF D w) = (D.mem u).A.T
        rw [prBelow_plF]; exact h⟩)
    rw [hLen u w, hdM, tauR_famOf L m A hτ, plB_plF]
    show (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * (L.tau w + ioPr L (LChain2.prBelow (plF D w)))
    rw [prBelow_plF, ioPr_resChar L hio]
    exact (hg1 u w hT).2
  · have hle : (famOf L m A).lenR u z / (famOf L m A).dM u ≤ (famOf L m A).lam u := by
      show (fam0 L m A).lenR u z / (fam0 L m A).dM u ≤
        ((fam0 L m A).ST u).fold max 0 (fun z => (fam0 L m A).lenR u z / (fam0 L m A).dM u)
      exact (Finset.le_fold_max _).2 (Or.inr ⟨z, hz, le_rfl⟩)
    calc (famOf L m A).lenR u z = (famOf L m A).dM u * ((famOf L m A).lenR u z / (famOf L m A).dM u) := by
          field_simp
      _ ≤ (famOf L m A).dM u * (famOf L m A).lam u := mul_le_mul_of_nonneg_left hle hdM0.le
  · show (0 : ℝ) ≤ ((fam0 L m A).ST u).fold max 0 (fun z => (fam0 L m A).lenR u z / (fam0 L m A).dM u)
    exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
  · have h1 := (D.ram_slopes u).1
    have h2 := (hSl u).1
    show ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL).mu = ((D.fm u).lat 0).mu - _
    rw [h1, h2]; rfl
  · have h1 := (D.ram_slopes u).2.1
    have h2 := (hSl u).2
    show ({ D.div.Nu u with L := DV.MramL D u } : HLat D.what₂.LL).muMax ≤ ((D.fm u).lat 0).muMax
    rw [h1]; exact h2

end Rec

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

variable {D : D7} (L : SizeData₂ D)

theorem sz_eq' (w : D.what₂.places.Pl) (y : ℝ) :
    SizeData₂.sz w y = 2 * (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * y) := by
  unfold SizeData₂.sz; ring

theorem rank_eq_card' {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)
    (h : Submodule.span K (A.L : Set A.V) = ⊤) : A.rank = Fintype.card A.ι := by
  unfold HLat.rank Formalism.HN.rkK
  rw [h, finrank_top, Module.finrank_eq_card_basis A.b]

section Sums
variable (m : ℕ) (A : Mx D)

theorem EeJ_famOf (u : D.what₂.Word) (j : Fin m) :
    (famOf L m A).EeJ u j = ∑ w ∈ L.supp, SizeData₂.sz w (L.E u (j.val + 1) w) := by
  show 2 * ∑ z ∈ SOf L, LChain2.lE z * L.E u (j.val + 1) (plB D z) = _
  have h := sum_SOf L (fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.E u (j.val + 1) w)
    (fun w hw => by rw [L.E_supp u _ w hw, mul_zero])
  rw [Finset.sum_congr rfl (fun z _ => by rw [lE_eq D z]), h, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _ => (sz_eq' w _).symm)

theorem Fo_famOf (hm : D.R.m = m) : (famOf L m A).Fo = L.Fo := by
  show 2 * ∑ j : Fin m, ∑ z ∈ SOf L, LChain2.lE z * L.F (j.val + 1) (plB D z) = _
  unfold SizeData₂.Fo
  rw [Lnk.sum_lifts D m hm (fun j => ∑ w ∈ L.supp, SizeData₂.sz w (L.F j w)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h := sum_SOf L (fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.F (j.val + 1) w)
    (fun w hw => by rw [L.F_supp _ w hw, mul_zero])
  rw [Finset.sum_congr rfl (fun z _ => by rw [lE_eq D z]), h, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _ => (sz_eq' w _).symm)

theorem tauR_eq (z : slopeLatticeData.FinPl D.what₂.LL) :
    (famOf L m A).tauR z = (⌊DV.ur D (plB D z) (L.tau (plB D z))⌋ : ℝ) / (D.what₂.places.ramIdx (plB D z) : ℝ) := by
  show (tauZ L z : ℝ) / LChain2.ramE z = _
  rw [tauZ_apply, ramE_eq]

theorem gamma_rounding : GaRounding := by
  intro D L m A hm
  show 2 * ∑ z ∈ SOf L, LChain2.lE z * ((∑ j : Fin m, L.gainD (j.val + 1) (plB D z)) - (famOf L m A).tauR z) = _
  have h := sum_SOf L (fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) *
      ((∑ j : Fin m, L.gainD (j.val + 1) w) -
        (⌊DV.ur D w (L.tau w)⌋ : ℝ) / (D.what₂.places.ramIdx w : ℝ)))
    (fun w hw => by
      rw [L.tau_supp w hw, Finset.sum_eq_zero (fun j _ => gainD_off L _ hw)]
      simp [DV.ur])
  rw [Finset.sum_congr rfl (fun z _ => by rw [lE_eq D z, tauR_eq]), h]
  unfold SizeData₂.Ga
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [sz_eq', Lnk.sum_lifts D m hm (fun j => L.gainD j w)]
  have he := (ramIdx_pos' w).ne'
  unfold DV.ur
  field_simp
  ring

theorem Ga_famOf (hm : D.R.m = m) (hτ : TauNat L) : (famOf L m A).Ga = L.Ga := by
  rw [gamma_rounding D L m A hm]
  have : ∑ w ∈ L.supp, 2 * SizeData₂.lwP w * (DV.ur D w (L.tau w) - (⌊DV.ur D w (L.tau w)⌋ : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    have h := tauZ_nat L hτ (plF D w)
    rw [tauZ_apply, plB_plF] at h
    rw [h]
    unfold DV.ur
    ring
  rw [this, add_zero]

theorem Ta_famOf (hτ : TauNat L) : (famOf L m A).Ta = ∑ w ∈ L.supp, SizeData₂.sz w (L.tau w) := by
  show 2 * ∑ z ∈ SOf L, LChain2.lE z * (famOf L m A).tauR z = _
  have h := sum_SOf L (fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.tau w)
    (fun w hw => by rw [L.tau_supp w hw, mul_zero])
  rw [Finset.sum_congr rfl (fun z _ => by rw [lE_eq D z, tauR_famOf L m A hτ]), h, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun w _ => (sz_eq' w _).symm)

theorem SOf_sat {z z' : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∈ SOf L) (h : LChain2.prBelow z' = LChain2.prBelow z) :
    z' ∈ SOf L := by
  rw [mem_SOf] at hz ⊢
  rw [h]; exact hz

theorem IO_famOf (hio : IoPrime L) :
    (famOf L m A).IO = ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.io w := by
  classical
  show ∑ p ∈ (SOf L).image LChain2.prBelow, Real.log (p : ℝ) * ioPr L p = _
  have h := sum_SOf L (fun w => SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.io w)
    (fun w hw => by rw [L.io_supp w hw, mul_zero])
  rw [← h]
  have h2 : ∑ z ∈ SOf L, SizeData₂.lwP (plB D z) * (D.what₂.places.ramIdx (plB D z) : ℝ) * L.io (plB D z) =
      ∑ p ∈ (SOf L).image LChain2.prBelow, ∑ z ∈ (SOf L).filter (fun z => LChain2.prBelow z = p),
        LChain2.lE z * ioPr L p := by
    rw [Finset.sum_image' (fun z => LChain2.lE z * ioPr L (LChain2.prBelow z))]
    · refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [lE_eq D z, prBelow_eq D z, ioPr_resChar L hio]
    · intro z _
      refine Finset.sum_congr rfl (fun z' hz' => ?_)
      rw [(Finset.mem_filter.1 hz').2]
  rw [h2]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
  rw [← Finset.sum_mul, LChain2.sum_log_norm_over_prime (SOf L) _ (LChain2.prBelow_prime z) (fun z' hz' => SOf_sat L hz hz')]

theorem del_famOf (hD : 0 < D.what₂.Dall) : (famOf L m A).del = D.what₂.delp := by
  show 1 - (Fintype.card D.div.RR.ι : ℝ) / (Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) : ℝ) = _
  have hκ : Fintype.card D.div.RR.ι = D.what₂.Drows := by
    rw [← Module.finrank_eq_card_basis D.div.RR.b, D.RRV_finrank]
  have hle := D.Drows_le_Dall hD
  have hα : Fintype.card (D.div.RR.ι ⊕ Fin (D.what₂.Dall - D.what₂.Drows)) = D.what₂.Dall := by
    rw [Fintype.card_sum, Fintype.card_fin, hκ]; omega
  rw [hα, hκ, D.what₂.D_eq]
  have : (0 : ℝ) < (D.what₂.Dall : ℝ) := by exact_mod_cast hD
  field_simp
  ring

end Sums

theorem localTie_of (hN : NprimeEq) : FieldwiseLocalAgreement := by
  intro D L m A hm hdef hfull hτ hio hD
  refine ⟨fun u => ⟨?_, rfl, ?_, ?_, rfl, rfl, rfl, fun j => EeJ_famOf L m A u j⟩, rfl, rfl, Fo_famOf L m A hm,
    Ga_famOf L m A hm hτ, Ta_famOf L m A hτ, IO_famOf L m A hio, del_famOf L m A hD⟩
  · show (Fintype.card (D.div.Nu u).ι : ℝ) = _
    rw [rank_eq_card' (D.div.Nu u) (hfull u).2]
  · rw [hN D L m A hdef u]; rfl
  · rw [hN D L m A hdef u]; rfl

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters
open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

namespace FieldEq

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top Top' : Type}
  [Fintype Top] [Fintype Top'] {m f f' : ℕ} {A : Data U0 W Top m f} {B : Data U0 W Top' m f'} {eT : Top ≃ Top'}
  {eF : Fin f ≃ Fin f'}

theorem ff (_h : FieldEq A B eT eF) : f = f' := by simpa using Fintype.card_congr eF

variable (h : FieldEq A B eT eF)
include h

theorem nT : A.nT = B.nT := by unfold Data.nT; rw [Fintype.card_congr eT]

theorem sumT (F : ℝ → ℝ) : ∑ t, F (A.aT t) = ∑ t, F (B.aT t) := by
  rw [← Equiv.sum_comp eT]; exact Finset.sum_congr rfl (fun t _ => by rw [h.aT])

theorem sumW (u0 : U0) (j : Fin m) (G : ℝ → ℝ) : ∑ ρ, G (A.w u0 j ρ) = ∑ ρ, G (B.w u0 j ρ) := by
  rw [← Equiv.sum_comp eF]; exact Finset.sum_congr rfl (fun t _ => by rw [h.w])

theorem fd : A.d = B.d := funext fun u0 => funext (h.d u0)
theorem fT : A.T = B.T := funext fun u0 => funext (h.T u0)
theorem fmuN : A.muN = B.muN := funext fun u0 => funext (h.muN u0)
theorem fmuMaxN : A.muMaxN = B.muMaxN := funext fun u0 => funext (h.muMaxN u0)
theorem fh : A.h = B.h := funext fun u0 => funext (h.h u0)
theorem fmuM : A.muM = B.muM := funext fun u0 => funext (h.muM u0)
theorem fmuMaxM : A.muMaxM = B.muMaxM := funext fun u0 => funext (h.muMaxM u0)
theorem fEeJ : A.EeJ = B.EeJ := funext fun u0 => funext fun u => funext (h.EeJ u0 u)
theorem fmuCC : A.muCC = B.muCC := funext h.muCC
theorem fmuMinCC : A.muMinCC = B.muMinCC := funext h.muMinCC
theorem fFo : A.Fo = B.Fo := funext h.Fo
theorem fGa : A.Ga = B.Ga := funext h.Ga
theorem fASK : A.ASK = B.ASK := funext h.ASK
theorem fIO : A.IO = B.IO := funext h.IO
theorem fHH : A.HH = B.HH := funext h.HH
theorem fdel : A.del = B.del := funext h.del
theorem fη : A.η = B.η := funext h.η
theorem fe : A.e = B.e := funext h.e

theorem sumA : A.sumA = B.sumA := h.sumT (fun y => y)

theorem logOm : A.logOm = B.logOm := by unfold Data.logOm; rw [h.gam, h.v, h.LpL]

theorem Ee (u0 : U0) (u : W u0) : A.Ee u0 u = B.Ee u0 u := by unfold Data.Ee; rw [h.fEeJ]

theorem s (u0 : U0) : A.s u0 = B.s u0 := by unfold Data.s; rw [h.fd, h.fmuN, h.fh]

theorem uF (u0 : U0) : A.uF u0 = B.uF u0 := by unfold Data.uF; rw [h.s, h.fmuMaxN, h.fh]

theorem LoP (C : Consts) : A.LoP C = B.LoP C := by unfold Data.LoP; rw [h.nT, h.b, h.x, h.ε]

theorem Lo5 (C : Consts) (Xpp : ℝ) (u0 : U0) (u : W u0) : Lo5 A C Xpp u0 u = Lo5 B C Xpp u0 u := by
  unfold WeightedSlopeBounds.Lo5; rw [h.fIO, h.nT, h.a, h.k, h.b', h.fT]

theorem setting (C : Consts) (hA : A.HidaSetting C) : B.HidaSetting C := by
  obtain rfl := h.ff
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hA
  rw [h.x] at a1
  rw [h.b] at a2
  rw [h.a] at a3
  rw [h.b'] at a4
  rw [h.k] at a5
  rw [h.v] at a6
  rw [h.fd] at a10
  rw [h.fT] at a11
  rw [h.fmuN, h.fmuMaxN] at a12
  rw [h.delBar] at a14
  rw [h.etaBar] at a15
  rw [h.eBar] at a16 a17
  refine ⟨a1, a2, a3, a4, a5, a6, a7, fun t => ?_, fun u0 j ρ => ?_, a10, a11, a12, a13, a14, a15, a16, a17⟩
  · have := a8 (eT.symm t); rwa [h.aT, Equiv.apply_symm_apply] at this
  · have := a9 u0 j (eF.symm ρ); rwa [h.w, Equiv.apply_symm_apply] at this

theorem div (C : Consts) (hA : A.DIV C) : B.DIV C := by
  intro u0 u
  have h1 := hA u0 u
  have e := h.sumT (fun y => (m : ℝ) * (ph y - y * B.logOm) - y * Real.log (B.T u0 u))
  rw [h.fmuCC, h.fh, h.fFo, h.logOm, h.fT, h.nT, h.a, h.La, h.B0, h.Nc, h.x, h.ε, e] at h1
  exact h1

theorem eComp5 (C : Consts) (hA : EComp5 A C) : EComp5 B C := by
  intro u0 u
  have h1 := hA u0 u
  rw [h.Ee, h.sumA, h.lg, h.B0] at h1
  exact h1

theorem hComp (C : Consts) (hA : A.HComp C) : B.HComp C := by
  intro u0 u u'
  have h1 := hA u0 u u'
  have e := h.sumT (fun y => y * Real.log (B.T u0 u))
  have e' := h.sumT (fun y => y * Real.log (B.T u0 u'))
  rw [h.fh, h.fT, h.nT, h.a, h.La, h.B0, e, e'] at h1
  exact h1

theorem count5 (C : Consts) (hA : Count5 A C) : Count5 B C := by
  obtain rfl := h.ff
  intro u0 u
  obtain ⟨h1, h2, h3⟩ := hA u0 u
  have e : ∀ j : Fin m, ∑ ρ, Real.log (A.w u0 j ρ * B.v / Real.pi) = ∑ ρ, Real.log (B.w u0 j ρ * B.v / Real.pi) :=
    fun j => h.sumW u0 j (fun y => Real.log (y * B.v / Real.pi))
  rw [h.v, h.lg, h.La, h.k, h.fT, Finset.sum_congr rfl (fun j _ => by rw [e j])] at h1
  rw [h.fT, h.L] at h2
  rw [h.fT, h.k] at h3
  exact ⟨h1, h2, h3⟩

theorem slopes (C : Consts) (hA : A.Slopes C) : B.Slopes C := by
  intro u0 u
  have h1 := hA u0 u
  rw [h.nT, h.a, h.La, h.k, h.fmuM, h.fmuMaxM] at h1
  exact h1

theorem slopes_transfer_field_eq (C : Consts) (Xpp : ℝ) (hA : QuotientSlopeBoundsWith A C Xpp) : QuotientSlopeBoundsWith B C Xpp := by
  intro u0 u
  have h1 := hA u0 u
  rw [h.fmuMaxN, h.fmuMaxM, h.fGa, h.fFo, h.Ee, h.B0, h.fmuM, h.Lo5, h.fmuN] at h1
  exact h1

theorem losses5 (C : Consts) (hA : LossBounds A C) : LossBounds B C := by
  intro u0
  have h1 := hA u0
  rw [h.fASK, h.fGa, h.LoP, h.fIO] at h1
  exact h1

theorem slopeIneq (hA : A.SlopeIneq) : B.SlopeIneq := by
  intro u0
  have h1 := hA u0
  rw [h.fdel, h.fη, h.fe, h.s, h.fmuMinCC, h.fHH, h.uF, h.fmuCC] at h1
  exact h1

theorem hhBound (C : Consts) (hA : A.HHBound C) : B.HHBound C := by
  intro u0
  have h1 := hA u0
  rw [h.s, h.fmuMinCC, h.fHH, h.x, h.b] at h1
  exact h1

theorem fParams (hA : A.FParams) : B.FParams := by
  intro u0
  have h1 := hA u0
  rw [h.fdel, h.fη, h.fe, h.delBar, h.etaBar, h.eBar] at h1
  exact h1

theorem sizeData₂ (C : Consts) (Xpp : ℝ) (hA : LChain.SizeData₂ A C Xpp) : LChain.SizeData₂ B C Xpp := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hA
  exact ⟨h.setting C a1, h.div C a2, h.eComp5 C a3, h.hComp C a4, h.count5 C a5, h.slopes C a6, h.slopes_transfer_field_eq C Xpp a7,
    h.losses5 C a8, h.slopeIneq a9, h.hhBound C a10, h.fParams a11⟩

theorem errWindows (C : Consts) (Xpp eK K : ℝ) (hA : ErrWindows A C Xpp eK K) : ErrWindows B C Xpp eK K := by
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hA
  rw [h.x] at w1 w5 w7 w8 w11 w14 w16
  rw [h.ε] at w2 w3 w7 w14 w16
  rw [h.b] at w4 w5
  rw [h.a] at w5 w12 w18 w20
  rw [h.nT] at w6
  rw [h.k] at w8 w10 w11 w12 w18 w24
  rw [h.L] at w13 w14
  rw [h.La] at w15 w16
  rw [h.b'] at w17 w18
  rw [h.B0] at w22
  rw [h.Nc] at w23
  rw [h.delBar] at w25
  rw [h.etaBar] at w26
  rw [h.eBar] at w27
  rw [h.etaBar, h.eBar, h.x, h.b, h.ε, h.nT, h.a] at wEta
  refine ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, fun t => ?_, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩
  have := w21 (eT.symm t)
  rwa [h.aT, Equiv.apply_symm_apply, h.a] at this

end FieldEq

theorem transfer_holds : Transfer := by
  intro U0 _ W _ _ Top Top' _ _ m f f' A B eT eF h C Xpp eK K
  exact ⟨h.sizeData₂ C Xpp, h.errWindows C Xpp eK K⟩

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters
open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

theorem local_first_layer_agreement : LocalFirstLayerAgreement := by
  intro eps Fm x e m pt A G cHH Dh ell N TT T2 a w h u0
  obtain ⟨hu, h1, h2, h3, h4, h5, h6, h7⟩ := h u0
  exact ⟨fun u => hu u, h1, h2, h3, h4, h5, h6, h7⟩

theorem logGamL_pos {D : D7} (L : SizeData₂ D) : 0 < Real.log (GamL L) := by
  unfold GamL
  rw [Real.log_exp]
  have h1 := L.CGam_pos
  have h2 : (0 : ℝ) < (D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have h3 : (0 : ℝ) < (D.R.f : ℝ) := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have h4 : 0 < L.sc.L := Real.rpow_pos_of_pos (lt_trans one_pos L.sc.one_lt_alt) _
  positivity

theorem global_first_layer_fails : GlobalFirstLayerFails := by
  intro eps Fm x e m pt A G cHH Dh ell N TT T2 a w Xpp η X' h
  have h1 := (h 0).2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 := logGamL_pos (Fm.L x (pt 0))
  rw [← h1] at h2
  exact lt_irrefl _ h2

section Mod

variable {eps : ℝ} {Fm : FamP eps} {x : ℝ} (M : Lnk.Mod Fm x) (hx : Fm.x1 < x)

include hx in
theorem sc_b : (Fm.L x M.i0).sc.b = bTx x eps := by
  show Real.exp ((Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps) = _
  rw [M.s_x hx, M.s_eps]; rfl

include hx in
theorem sc_a : (Fm.L x M.i0).sc.a = aTx x eps := by
  show (Fm.L x M.i0).sc.x * (Fm.L x M.i0).sc.b = _
  rw [M.s_x hx, sc_b M hx]; rfl

include hx in
theorem sc_Xp : (Fm.L x M.i0).sc.X' = XpTx x eps := by
  show Real.exp ((Fm.L x M.i0).sc.x ^ ((Fm.L x M.i0).sc.eps / 3)) = _
  rw [M.s_x hx, M.s_eps]; rfl

include hx in
theorem sc_bp : (Fm.L x M.i0).sc.b' = bpTx x eps := by
  show (Fm.L x M.i0).sc.a / (Fm.L x M.i0).sc.X' = _
  rw [sc_a M hx, sc_Xp M hx]; rfl

include hx in
theorem sc_L : (Fm.L x M.i0).sc.L = Real.log (bTx x eps) := by
  unfold bTx
  rw [Real.log_exp]
  show (Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps = _
  rw [M.s_x hx, M.s_eps]

theorem card_n : (Fintype.card M.e.A : ℝ) = ((Fm.D x M.i0).R.n : ℝ) := by
  rw [Lnk.card_HA]; rfl

include hx in
theorem sc_Xpp (etaB eB : ℝ) :
    (Fm.L x M.i0).sc.X'' (Fm.D x M.i0).R.n = LChain2.XppH M.e.A (globM M etaB eB) := by
  show (Fm.L x M.i0).sc.a / ((Fm.L x M.i0).sc.b' / ((Fm.L x M.i0).sc.x * ((Fm.D x M.i0).R.n : ℝ))) =
    aTx x eps / (bpTx x eps / (x * (Fintype.card M.e.A : ℝ)))
  rw [sc_a M hx, sc_bp M hx, M.s_x hx, card_n]

include hx in
theorem base_bound_eq : (Fm.L x M.i0).B0 = (2 * (Fintype.card M.e.A : ℝ)) * M.m * bTx x eps * x ^ eps := by
  show (((Fm.D x M.i0).R.f : ℕ) : ℝ) * ((Fm.D x M.i0).R.m : ℝ) *
    Real.exp ((Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps) * (Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps = _
  rw [M.s_x hx, M.s_eps, card_n]
  have : (((Fm.D x M.i0).R.f : ℕ) : ℝ) = 2 * ((Fm.D x M.i0).R.n : ℝ) := by
    unfold Ranks.f; push_cast; ring
  rw [this]; rfl

include hx in
theorem Nc_eq' : (Fm.L x M.i0).Nc = (M.T2.card : ℝ) * ((Fm.D x M.i0).R.k : ℝ) * bTx x eps * x ^ eps
    / ((Fintype.card M.e.A : ℝ) * ((Fintype.card M.e.A : ℝ) * x ^ (-eps))) := by
  show ((Fm.D x M.i0).host.T2.card : ℝ) * ((Fm.D x M.i0).R.k : ℝ) *
    Real.exp ((Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps) * (Fm.L x M.i0).sc.x ^ (Fm.L x M.i0).sc.eps /
    (((Fm.D x M.i0).R.n : ℝ) * (((Fm.D x M.i0).R.n : ℝ) * (Fm.L x M.i0).sc.x ^ (-(Fm.L x M.i0).sc.eps))) = _
  rw [M.s_x hx, M.s_eps, card_n, M.card_thick_set_model_eq]; rfl

theorem modified_field_eq : ModFieldEq := by
  intro eps Fm x M A ell N CH etaB eB hx hl hT
  exact
  { x := rfl
    ε := rfl
    a := sc_a M hx
    b := sc_b M hx
    b' := sc_bp M hx
    k := rfl
    L := sc_L M hx
    La := rfl
    B0 := base_bound_eq M hx
    Nc := Nc_eq' M hx
    gam := rfl
    LpL := hl
    v := rfl
    lg := rfl
    aT := fun τ => (M.ident N CH etaB eB (etaM M A CH) (eM M A) ell hl).1 τ
    w := fun u0 j ρ => by
      show M.w u0 j (M.eP ρ).1 = M.w u0 j (LChain2.ePhi (LChain2.ePhi.symm (M.eP ρ))).1
      rw [Equiv.apply_symm_apply]
    d := fun u0 u => ((hT u0).1 u).1.symm
    T := fun u0 u => ((hT u0).1 u).2.1.symm
    muN := fun u0 u => ((hT u0).1 u).2.2.1.symm
    muMaxN := fun u0 u => ((hT u0).1 u).2.2.2.1.symm
    h := fun u0 u => ((hT u0).1 u).2.2.2.2.1.symm
    muM := fun u0 u => ((hT u0).1 u).2.2.2.2.2.1.symm
    muMaxM := fun u0 u => ((hT u0).1 u).2.2.2.2.2.2.1.symm
    EeJ := fun u0 u j => (((hT u0).1 u).2.2.2.2.2.2.2 j).symm
    muCC := fun u0 => (hT u0).2.1.symm
    muMinCC := fun u0 => (hT u0).2.2.1.symm
    Fo := fun u0 => (hT u0).2.2.2.1.symm
    Ga := fun u0 => (hT u0).2.2.2.2.1.symm
    Ta := fun u0 => (hT u0).2.2.2.2.2.1.symm
    ASK := fun _ => rfl
    IO := fun u0 => (hT u0).2.2.2.2.2.2.1.symm
    HH := fun _ => by
      show x ^ CH * (Fm.L x M.i0).sc.b = x ^ CH * bTx x eps
      rw [sc_b M hx]
    del := fun u0 => (hT u0).2.2.2.2.2.2.2.symm
    η := fun _ => rfl
    e := fun _ => rfl
    delBar := rfl
    etaBar := rfl
    eBar := rfl }

theorem card_f (u0 : M.e.A) : (Fm.D x (M.pt u0)).R.f = (PhiSet (H := M.e.A)).card := by
  rw [M.hf u0, Lnk.card_PhiSet]; rfl

theorem second_chain_of_modified : Chain2OfMod := by
  intro eps Fm x M A ell C cT N η θ etaB eB eK K CL hx hl hT hSet hDIV hEC hHC hCnt hSl hLoss hHH hFP hWin hRest hCost
    hSize hLat hPl hSz
  have hE := modified_field_eq M A ell N C.cHH etaB eB hx hl hT
  have a1 := hE.setting C hSet
  have a2 := hE.div C hDIV
  have a3 := hE.eComp5 C hEC
  have a4 := hE.hComp C hHC
  have a5 := hE.count5 C hCnt
  have a6 := hE.slopes C hSl
  have a8 := hE.losses5 C hLoss
  have a10 := hE.hhBound C hHH
  have hWin' := hE.errWindows C _ eK K hWin
  rw [sc_Xpp M hx etaB eB] at hWin'
  rw [sc_b M hx, sc_bp M hx, sc_Xp M hx] at hRest
  rw [sc_b M hx] at hCost
  rw [sc_b M hx, sc_a M hx] at hSize
  refine ⟨⟨hLat, fun u0 => ?_, hSz, a1.2.2.2.2.2.1, a1.2.2.2.2.2.2.2.2.2.1, a1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, a2, a3, a4, a5,
    a6, fun u0 => (a10 u0).1, fun u0 => ⟨(hE.del u0).symm.trans_le (hFP u0).1, (hFP u0).2.1, (hFP u0).2.2⟩, hWin', hRest,
    hCost, hSize⟩, a8⟩
  have h := hPl u0
  rw [card_f M u0, M.s_sc hx u0, sc_b M hx] at h
  exact h

end Mod

theorem second_chain_record : Chain2RecCore := by
  intro eps Fm eD eL K cHH eK CL x hF
  rintro ⟨M, A, ell, C, cT, N, η, θ, etaB, eB, h1, h2, h3, -, -, -, hI⟩
  exact ⟨M.e.A, inferInstance, inferInstance, inferInstance, fun u0 => (Fm.D x (M.pt u0)).what₂.Word,
    fun _ => inferInstance, fun _ => inferInstance, M.m, M.AD, ell, globM M etaB eB, C, cT, N, M.TT, M.T2,
    M.a, M.w, famM M A, η, θ, rfl, rfl, h1, h2, h3, hF M.i0, hI⟩

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters
open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

set_option maxHeartbeats 1600000 in
theorem second_chain_record_tied : ChainRecordCompatible := by
  intro eps Fm eD eL K cHH eK CL x hx hTie
  rintro ⟨M, A, ell, C, cT, N, η, θ, etaB, eB, h1, h2, h3, hAr, hl, hη, hI⟩
  have hT : ∀ u0, LocalTie (Fm.L x (M.pt u0)) M.m (famM M A u0) := fun u0 => hTie (M.pt u0) M.m (A u0) (M.hm u0)
  have hE := modified_field_eq M A ell N C.cHH etaB eB hx hl hT
  obtain ⟨hB, hLoss⟩ := hI
  obtain ⟨l1, l7, l9, l10, l11⟩ := LChain2.sizeConditions_of_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB
  obtain ⟨-, -, -, -, -, -, hDIV, hEC, hHC, hCnt, hSl, -, -, hWin, hRest, hCost, hSize⟩ := hB
  refine ⟨M.i0, M.m, (PhiSet (H := M.e.A)).card, M.pt, M.av, M.bv, ↥M.TT,
    inferInstance, { dataK M A ell N C.cHH etaB eB with logGam := Real.log (GamL (Fm.L x M.i0)) }, C,
    LChain2.XppH M.e.A (globM M etaB eB), ell, N, M.TT, M.T2, M.a, M.w, Equiv.refl _, LChain2.ePhi, η, XpTx x eps, θ,
    ?_, ?_, ?_, hAr, rfl, rfl, h1, h2, h3, ?_, ?_, hWin, ?_,
    hRest, hCost, hSize⟩
  · intro u0
    obtain ⟨t1, t2, -, t4, t5, t6, t7⟩ := M.tiePts u0
    exact ⟨t1, t2, card_f M u0, t4, t5, t6, t7⟩
  · intro u0
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩ :=
      M.tieGlobal hx N C.cHH etaB eB (etaM M A C.cHH) (eM M A) u0
    exact ⟨hE.a.symm.trans g1, hE.b.symm.trans g2, hE.b'.symm.trans g3, hE.k.symm.trans g4, hE.L.symm.trans g5,
      hE.La.symm.trans g6, hE.B0.symm.trans g7, hE.Nc.symm.trans g8, rfl, hE.LpL.symm.trans g10, hE.v.symm.trans g11,
      hE.lg.symm.trans g12, g13, (sc_Xpp M hx etaB eB).symm.trans g14, hη.trans g15, (sc_Xp M hx).symm.trans g16⟩
  · exact local_first_layer_agreement Fm x M.e M.m M.pt A (globM M etaB eB) C.cHH M.AD ell N M.TT M.T2 M.a M.w hT
  · exact ⟨fun _ => rfl, fun _ _ _ => rfl, rfl, rfl, fun _ => rfl⟩
  · exact ⟨l1, hDIV, hEC, hHC, hCnt, hSl, l7, hLoss, l9, l10, l11⟩
  · exact ⟨le_refl _, le_refl _⟩

end Formalism.L2.GlobalTheoryTheory.FamRec

end

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.HN Formalism.LFunctionChainParameters

variable {D : D7} (L : SizeData₂ D) (m : ℕ) (A : Mx D)

theorem sgw_famOf (hm : D.R.m = m) (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    (famOf L m A).sgw u z = L.sg u (plB D z) := by
  show ∑ j : Fin m, (L.gainD (j.val + 1) (plB D z) + L.F (j.val + 1) (plB D z) - L.E u (j.val + 1) (plB D z)) = _
  unfold SizeData₂.sg
  rw [Lnk.sum_lifts D m hm (fun j => L.gainD j (plB D z) + L.F j (plB D z) - L.E u j (plB D z))]

theorem sgR_famOf (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    (famOf L m A).sgR u z =
      (⌊DV.ur D (plB D z) (L.sg u (plB D z))⌋ : ℝ) / (D.what₂.places.ramIdx (plB D z) : ℝ) := by
  show (sgZ L u z : ℝ) / LChain2.ramE z = _
  rw [sgZ_apply, ramE_eq]

theorem sgR_le (hm : D.R.m = m) (u : D.what₂.Word) (z : slopeLatticeData.FinPl D.what₂.LL) :
    (famOf L m A).sgR u z ≤ (famOf L m A).sgw u z := by
  rw [sgR_famOf, sgw_famOf L m A hm, div_le_iff₀ (ramIdx_pos' _), mul_comm]
  exact Int.floor_le _

theorem Rd_famOf (hm : D.R.m = m) (u : D.what₂.Word) :
    (famOf L m A).Rd u = ∑ w ∈ L.supp, 2 * SizeData₂.lwP w * Int.fract (DV.ur D w (L.sg u w)) := by
  show ∑ z ∈ SOf L, 2 * LChain2.lE z * ((famOf L m A).sgw u z - (famOf L m A).sgR u z) = _
  have h := sum_SOf L (fun w => 2 * SizeData₂.lwP w * Int.fract (DV.ur D w (L.sg u w)))
    (fun w hw => by rw [sg_off L u hw]; simp [DV.ur])
  rw [← h]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [sgw_famOf L m A hm, sgR_famOf, lE_eq]
  have he := (ramIdx_pos' (plB D z)).ne'
  unfold Int.fract DV.ur
  field_simp

theorem Rd_eq_abs (hm : D.R.m = m) (hdef : DV.NprimeDef D L) (u : D.what₂.Word) (hfg : (D.div.Nu u).L.FG)
    (hne : (D.div.Nu u).L ≠ ⊥) :
    (famOf L m A).Rd u = |(D.div.Nu u).mu - (L.NuH u).mu - ∑ w ∈ L.supp, SizeData₂.sz w (L.sg u w)| := by
  rw [J.mu_diff D L hdef u (D.div_good.2 u) hfg hne, ← Finset.sum_sub_distrib, Rd_famOf L m A hm]
  have h : ∀ w ∈ L.supp, 2 * SizeData₂.lwP w * (⌊DV.ur D w (L.sg u w)⌋ : ℝ) - SizeData₂.sz w (L.sg u w) =
      -(2 * SizeData₂.lwP w * Int.fract (DV.ur D w (L.sg u w))) := by
    intro w _
    unfold SizeData₂.sz Int.fract DV.ur
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib, abs_neg, abs_of_nonneg]
  exact Finset.sum_nonneg (fun w _ => mul_nonneg (mul_nonneg (by norm_num) (J.logWeight_nonneg w)) (Int.fract_nonneg _))

theorem Rd_le_of_mu (hm : D.R.m = m) (hdef : DV.NprimeDef D L) (hfull : D.NuFull)
    (hrk : ∀ u, 0 < (D.div.Nu u).rank) (C : ℝ) (hMu : NprimeMuR L C) (u : D.what₂.Word) :
    (famOf L m A).Rd u ≤ C * L.sc.X'' D.R.n := by
  rw [Rd_eq_abs L m A hm hdef u (hfull u).1 (J.ne_bot_of_rank_pos _ (hrk u))]
  exact hMu u

theorem lam_nonneg (u : D.what₂.Word) : 0 ≤ (famOf L m A).lam u := by
  show 0 ≤ lamOf L m A u
  unfold lamOf
  exact Finset.le_fold_max 0 |>.2 (Or.inl (le_refl _))

theorem le_lam (u : D.what₂.Word) {z : slopeLatticeData.FinPl D.what₂.LL} (hz : z ∈ (famOf L m A).ST u) :
    (famOf L m A).lenR u z / (famOf L m A).dM u ≤ (famOf L m A).lam u := by
  show _ ≤ lamOf L m A u
  unfold lamOf
  exact Finset.le_fold_max _ |>.2 (Or.inr ⟨z, hz, le_refl _⟩)

theorem lam_le (hLen : ∀ u w, (famOf L m A).lenR u (plF D w) = (L.lenMN u w : ℝ))
    (hcard : ∀ u, Fintype.card ((D.fm u).lat 0).ι = D.duS u) (u : D.what₂.Word) (hd : 0 < D.duS u) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (L.lenMN u w : ℝ) ≤ (D.duS u : ℝ) * c) :
    (famOf L m A).lam u ≤ c := by
  show lamOf L m A u ≤ c
  unfold lamOf
  refine Finset.fold_max_le _ |>.2 ⟨hc, fun z hz => ?_⟩
  have hzT0 : LChain2.prBelow z = (D.mem u).A.T := (Finset.mem_filter.1 hz).2
  have hzT : D.what₂.places.resChar (plB D z) = (D.mem u).A.T := (prBelow_eq D z).symm.trans hzT0
  have h1 := h (plB D z) hzT
  have h2 := hLen u (plB D z)
  have h3 : (fam0 L m A).lenR u z = (L.lenMN u (plB D z) : ℝ) :=
    (congrArg (fun y => (famOf L m A).lenR u y) (plF_plB D z)).symm.trans h2
  have hdM : (fam0 L m A).dM u = (D.duS u : ℝ) := by
    show (Fintype.card ((D.fm u).lat 0).ι : ℝ) = _
    rw [hcard u]
  have hpos : (0 : ℝ) < (D.duS u : ℝ) := by exact_mod_cast hd
  rw [hdM, div_le_iff₀ hpos, h3, mul_comm]
  exact h1

end Formalism.L2.GlobalTheoryTheory.FamRec

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamRec

theorem fieldwise_local_agreement : FieldwiseLocalAgreement := localTie_of lattice_N_prime_eq

theorem length_eq_alt : LenEq := lenEq_of length_twist

theorem place_facts_small : PlaceHypothesisOfPlaceSizes := place_facts_of_twist_length length_twist

end Formalism.L2.GlobalTheoryTheory.FamRec

end
