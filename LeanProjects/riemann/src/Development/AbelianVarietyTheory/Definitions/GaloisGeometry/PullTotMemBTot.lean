import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory KaehlerDifferential

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

universe v u v' u' v'' u''

section Complex

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)

def OmF (q : ℕ) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (Om R (F.obj T) q)
  map φ := ModuleCat.ofHom (pOm F q φ)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_id F x)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ pOm_comp F φ ψ x)

def dOmNat (q : ℕ) : OmF F q ⟶ OmF F (q + 1) where
  app T := ModuleCat.ofHom (dOm R (F.obj T) q)
  naturality _ _ φ := ModuleCat.hom_ext (LinearMap.ext fun x ↦ (pOm_dOm F φ x).symm)

abbrev Term (a q : ℕ) : Type (max u v) := CatH.Cn (OmF F q) a

abbrev dH (a q : ℕ) : Term F a q →ₗ[R] Term F (a + 1) q := CatH.d (OmF F q) a

def dV (a q : ℕ) : Term F a q →ₗ[R] Term F a (q + 1) :=
  (CatH.Mor.ofNatTrans (dOmNat F q)).pullC a

theorem dV_apply {a q : ℕ} (c : Term F a q) (s : ComposableArrows C a) :
    dV F a q c s = dOm R (F.obj (s.obj (Fin.last a))) q (c s) := rfl

abbrev Bidegree (n : ℕ) : Type := {p : ℕ × ℕ // p.1 + p.2 = n}

abbrev Tot (n : ℕ) : Type (max u v) := ∀ p : Bidegree n, Term F p.1.1 p.1.2

def totH (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(0, _), _⟩ => 0
    | ⟨(a + 1, q), h⟩ => dH F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n)

def totV (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) :=
  LinearMap.pi fun p ↦ match p with
    | ⟨(_, 0), _⟩ => 0
    | ⟨(a, q + 1), h⟩ => (-1 : ℤ) ^ a • (dV F a q ∘ₗ LinearMap.proj (⟨(a, q), by omega⟩ : Bidegree n))

def dTot (n : ℕ) : Tot F n →ₗ[R] Tot F (n + 1) := totH F n + totV F n

section
variable {F} {n : ℕ} (c : Tot F n)

@[simp] theorem totH_zero {q : ℕ} (h : 0 + q = n + 1) : totH F n c ⟨(0, q), h⟩ = 0 := rfl

@[simp] theorem totH_succ {a q : ℕ} (h : a + 1 + q = n + 1) :
    totH F n c ⟨(a + 1, q), h⟩ = dH F a q (c ⟨(a, q), by omega⟩) := rfl

@[simp] theorem totV_zero {a : ℕ} (h : a + 0 = n + 1) : totV F n c ⟨(a, 0), h⟩ = 0 := rfl

@[simp] theorem totV_succ {a q : ℕ} (h : a + (q + 1) = n + 1) :
    totV F n c ⟨(a, q + 1), h⟩ = (-1 : ℤ) ^ a • dV F a q (c ⟨(a, q), by omega⟩) := rfl

theorem dTot_apply (p : Bidegree (n + 1)) : dTot F n c p = totH F n c p + totV F n c p := rfl

end

def ZTot (n : ℕ) : Submodule R (Tot F n) := LinearMap.ker (dTot F n)

def BTot : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dTot F n)

def Hyp (n : ℕ) : Type (max u v) := ZTot F n ⧸ (BTot F n).submoduleOf (ZTot F n)

instance (n : ℕ) : AddCommGroup (Hyp F n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (n : ℕ) : Module R (Hyp F n) := inferInstanceAs (Module R (_ ⧸ _))

def Hyp.mk (n : ℕ) : ZTot F n →ₗ[R] Hyp F n := Submodule.mkQ _

theorem Hyp.mk_surjective (n : ℕ) : Function.Surjective (Hyp.mk F n) := Submodule.mkQ_surjective _

variable {F} in

theorem Hyp.mk_eq_zero {n : ℕ} {c : ZTot F n} : Hyp.mk F n c = 0 ↔ c.1 ∈ BTot F n :=
  Submodule.Quotient.mk_eq_zero _

def TotF (p n : ℕ) : Submodule R (Tot F n) where
  carrier := {c | ∀ b : Bidegree n, b.1.2 < p → c b = 0}
  add_mem' hc hc' b hb := by rw [Pi.add_apply, hc b hb, hc' b hb, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' r c hc b hb := by rw [Pi.smul_apply, hc b hb, smul_zero]

theorem TotF_anti {p p' : ℕ} (h : p ≤ p') (n : ℕ) : TotF F p' n ≤ TotF F p n :=
  fun _ hc b hb ↦ hc b (hb.trans_le h)

theorem TotF_zero (n : ℕ) : TotF F 0 n = ⊤ :=
  eq_top_iff.2 fun _ _ _ hb ↦ absurd hb (Nat.not_lt_zero _)

theorem TotF_eq_bot {p n : ℕ} (h : n < p) : TotF F p n = ⊥ :=
  eq_bot_iff.2 fun _ hc ↦ funext fun b ↦ hc b (by have := b.2; omega)

def ZF (p n : ℕ) : Submodule R (Tot F n) := TotF F p n ⊓ ZTot F n

def BF (p : ℕ) : ∀ n : ℕ, Submodule R (Tot F n)
  | 0 => ⊥
  | n + 1 => (TotF F p n).map (dTot F n)

theorem BF_le_BTot (p : ℕ) : ∀ n : ℕ, BF F p n ≤ BTot F n
  | 0 => le_rfl
  | _ + 1 => LinearMap.map_le_range

theorem BF_anti {p p' : ℕ} (h : p ≤ p') : ∀ n : ℕ, BF F p' n ≤ BF F p n
  | 0 => le_rfl
  | n + 1 => Submodule.map_mono (TotF_anti F h n)

def HypF (p n : ℕ) : Type (max u v) := ZF F p n ⧸ (BF F p n).submoduleOf (ZF F p n)

instance (p n : ℕ) : AddCommGroup (HypF F p n) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (p n : ℕ) : Module R (HypF F p n) := inferInstanceAs (Module R (_ ⧸ _))

def HypF.mk (p n : ℕ) : ZF F p n →ₗ[R] HypF F p n := Submodule.mkQ _

theorem HypF.mk_surjective (p n : ℕ) : Function.Surjective (HypF.mk F p n) :=
  Submodule.mkQ_surjective _

variable {F} in

theorem HypF.mk_eq_zero {p n : ℕ} {c : ZF F p n} : HypF.mk F p n c = 0 ↔ c.1 ∈ BF F p n :=
  Submodule.Quotient.mk_eq_zero _

def HypF.toHyp (p n : ℕ) : HypF F p n →ₗ[R] Hyp F n :=
  Submodule.mapQ _ _ (Submodule.inclusion inf_le_right) fun _ hc ↦ BF_le_BTot F p n hc

def HypF.incl {p p' : ℕ} (h : p ≤ p') (n : ℕ) : HypF F p' n →ₗ[R] HypF F p n :=
  Submodule.mapQ _ _ (Submodule.inclusion (inf_le_inf_right _ (TotF_anti F h n)))
    fun _ hc ↦ BF_anti F h n hc

theorem HypF.toHyp_incl {p p' : ℕ} (h : p ≤ p') (n : ℕ) (c : HypF F p' n) :
    HypF.toHyp F p n (HypF.incl F h n c) = HypF.toHyp F p' n c := by
  obtain ⟨c, rfl⟩ := HypF.mk_surjective F p' n c; rfl

def Hyp.fil (p n : ℕ) : Submodule R (Hyp F n) := LinearMap.range (HypF.toHyp F p n)

variable {F} in

theorem Hyp.mem_fil {p n : ℕ} {x : Hyp F n} :
    x ∈ Hyp.fil F p n ↔ ∃ c : ZTot F n, c.1 ∈ TotF F p n ∧ Hyp.mk F n c = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := HypF.mk_surjective F p n y
    exact ⟨⟨c.1, c.2.2⟩, c.2.1, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨HypF.mk F p n ⟨c.1, hc, c.2⟩, rfl⟩

theorem Hyp.fil_anti {p p' : ℕ} (h : p ≤ p') (n : ℕ) : Hyp.fil F p' n ≤ Hyp.fil F p n := by
  rintro _ ⟨c, rfl⟩
  exact ⟨_, HypF.toHyp_incl F h n c⟩

theorem Hyp.fil_zero (n : ℕ) : Hyp.fil F 0 n = ⊤ := eq_top_iff.2 fun x _ ↦ by
  obtain ⟨c, rfl⟩ := Hyp.mk_surjective F n x
  exact Hyp.mem_fil.2 ⟨c, by rw [TotF_zero]; trivial, rfl⟩

theorem Hyp.fil_eq_bot {p n : ℕ} (h : n < p) : Hyp.fil F p n = ⊥ := eq_bot_iff.2 fun x hx ↦ by
  obtain ⟨c, hc, rfl⟩ := Hyp.mem_fil.1 hx
  rw [TotF_eq_bot F h] at hc
  rw [show c = 0 from Subtype.ext hc, map_zero]; rfl

theorem dH_lead {a p n : ℕ} (h : a + p = n) (c : ZF F p n) : dH F a p (c.1 ⟨(a, p), h⟩) = 0 := by
  have e := congrFun (show dTot F n c.1 = 0 from c.2.2) ⟨(a + 1, p), by omega⟩
  have hV : totV F n c.1 ⟨(a + 1, p), by omega⟩ = 0 := by
    rcases p with _ | p
    · rfl
    · rw [totV_succ, c.2.1 _ (Nat.lt_succ_self p), map_zero, smul_zero]
  rwa [dTot_apply, hV, add_zero] at e

def leadZ {a p n : ℕ} (h : a + p = n) : ZF F p n →ₗ[R] LinearMap.ker (CatH.d (OmF F p) a) :=
  ((LinearMap.proj (⟨(a, p), h⟩ : Bidegree n)) ∘ₗ (ZF F p n).subtype).codRestrict _ (dH_lead F h)

def HypF.lead {a p n : ℕ} (h : a + p = n) : HypF F p n →ₗ[R] CatH.H (OmF F p) a :=
  Submodule.mapQ _ _ (leadZ F h) (by
    intro c hc
    change c.1 ⟨(a, p), h⟩ ∈ CatH.Bn (OmF F p) a
    have hc' : c.1 ∈ BF F p n := hc
    rcases n with _ | n
    · rw [show c.1 = 0 from hc']; exact zero_mem _
    obtain ⟨e, he, hd⟩ := hc'
    have hV : totV F n e ⟨(a, p), h⟩ = 0 := by
      rcases p with _ | p
      · rfl
      · rw [totV_succ, he _ (Nat.lt_succ_self p), map_zero, smul_zero]
    rw [← hd, dTot_apply, hV, add_zero]
    rcases a with _ | a
    · exact zero_mem _
    · exact ⟨_, rfl⟩)

end Complex

section Pull

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
  {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''} (m : CoefMap σ F F')

def omMor (q : ℕ) : CatH.Mor (OmF F q) (OmF F' q) σ where
  G := m.G
  τ T := qOm m q T
  nat φ x := qOm_pOm m φ x

abbrev pullTerm (a q : ℕ) : Term F a q →ₛₗ[σ] Term F' a q := (omMor m q).pullC a

theorem dH_pullTerm {a q : ℕ} (c : Term F a q) :
    dH F' a q (pullTerm m a q c) = pullTerm m (a + 1) q (dH F a q c) := (omMor m q).d_pullC a c

theorem dV_pullTerm {a q : ℕ} (c : Term F a q) :
    dV F' a q (pullTerm m a q c) = pullTerm m a (q + 1) (dV F a q c) :=
  funext fun s ↦ ((semiHom_coef m _).mOm_dOm (c (s ⋙ m.G))).symm

def pullTot (n : ℕ) : Tot F n →ₛₗ[σ] Tot F' n where
  toFun c b := pullTerm m _ _ (c b)
  map_add' c c' := funext fun b ↦ map_add _ (c b) (c' b)
  map_smul' r c := funext fun b ↦ map_smulₛₗ (pullTerm m _ _) r (c b)

theorem pullTot_apply {n : ℕ} (c : Tot F n) (b : Bidegree n) :
    pullTot m n c b = pullTerm m _ _ (c b) := rfl

theorem dTot_pullTot {n : ℕ} (c : Tot F n) :
    dTot F' n (pullTot m n c) = pullTot m (n + 1) (dTot F n c) := by
  funext ⟨(a, q), h⟩
  rw [pullTot_apply, dTot_apply, dTot_apply, map_add]
  congr 1
  · rcases a with _ | a
    · exact (map_zero _).symm
    · exact dH_pullTerm m _
  · rcases q with _ | q
    · exact (map_zero _).symm
    · rw [totV_succ, totV_succ, map_zsmul, pullTot_apply, dV_pullTerm]

theorem pullTot_mem_ZTot {n : ℕ} {c : Tot F n} (hc : c ∈ ZTot F n) : pullTot m n c ∈ ZTot F' n := by
  change dTot F' n _ = 0
  rw [dTot_pullTot, show dTot F n c = 0 from hc, map_zero]

theorem pullTot_mem_TotF {p n : ℕ} {c : Tot F n} (hc : c ∈ TotF F p n) :
    pullTot m n c ∈ TotF F' p n := fun b hb ↦ by rw [pullTot_apply, hc b hb, map_zero]

theorem pullTot_mem_BTot : ∀ {n : ℕ} {c : Tot F n}, c ∈ BTot F n → pullTot m n c ∈ BTot F' n
  | 0, c, hc => by rw [show c = 0 from hc, map_zero]; exact zero_mem _
  | _ + 1, _, ⟨e, he⟩ => ⟨_, (dTot_pullTot m e).trans (congrArg _ he)⟩

theorem pullTot_mem_BF {p : ℕ} : ∀ {n : ℕ} {c : Tot F n}, c ∈ BF F p n → pullTot m n c ∈ BF F' p n
  | 0, c, hc => by rw [show c = 0 from hc, map_zero]; exact zero_mem _
  | _ + 1, _, ⟨e, h, he⟩ => ⟨_, pullTot_mem_TotF m h, (dTot_pullTot m e).trans (congrArg _ he)⟩

def pullZ (n : ℕ) : ZTot F n →ₛₗ[σ] ZTot F' n :=
  ((pullTot m n).domRestrict _).codRestrict _ fun c ↦ pullTot_mem_ZTot m c.2

def pullZF (p n : ℕ) : ZF F p n →ₛₗ[σ] ZF F' p n :=
  ((pullTot m n).domRestrict _).codRestrict _ fun c ↦
    ⟨pullTot_mem_TotF m c.2.1, pullTot_mem_ZTot m c.2.2⟩

def Hyp.pull (n : ℕ) : Hyp F n →ₛₗ[σ] Hyp F' n :=
  Submodule.mapQ _ _ (pullZ m n) fun _ hc ↦ pullTot_mem_BTot m hc

def HypF.pull (p n : ℕ) : HypF F p n →ₛₗ[σ] HypF F' p n :=
  Submodule.mapQ _ _ (pullZF m p n) fun _ hc ↦ pullTot_mem_BF m hc

theorem HypF.toHyp_pull {p n : ℕ} (c : HypF F p n) :
    HypF.toHyp F' p n (HypF.pull m p n c) = Hyp.pull m n (HypF.toHyp F p n c) := by
  obtain ⟨c, rfl⟩ := HypF.mk_surjective F p n c; rfl

theorem Hyp.pull_mem_fil {p n : ℕ} {x : Hyp F n} (hx : x ∈ Hyp.fil F p n) :
    Hyp.pull m n x ∈ Hyp.fil F' p n := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨_, HypF.toHyp_pull m c⟩

theorem pullTot_id {n : ℕ} (c : Tot F n) : pullTot (CoefMap.id F) n c = c :=
  funext fun b ↦ funext fun s ↦ SemiHom.mOm_id _ (fun _ ↦ rfl) (c b s)

theorem pullTot_comp (m' : CoefMap τ F' F'') {n : ℕ} (c : Tot F n) :
    pullTot (m.comp m') n c = pullTot m' n (pullTot m n c) :=
  funext fun b ↦ funext fun s ↦
    (SemiHom.mOm_mOm (semiHom_coef m _) (semiHom_coef m' _) _ (fun _ ↦ rfl)
      (c b (s ⋙ m'.G ⋙ m.G))).symm

theorem Hyp.pull_id {n : ℕ} (x : Hyp F n) : Hyp.pull (CoefMap.id F) n x = x := by
  obtain ⟨c, rfl⟩ := Hyp.mk_surjective F n x
  exact congrArg (Hyp.mk F n) (Subtype.ext (pullTot_id c.1))

theorem Hyp.pull_comp (m' : CoefMap τ F' F'') {n : ℕ} (x : Hyp F n) :
    Hyp.pull (m.comp m') n x = Hyp.pull m' n (Hyp.pull m n x) := by
  obtain ⟨c, rfl⟩ := Hyp.mk_surjective F n x
  exact congrArg (Hyp.mk F'' n) (Subtype.ext (pullTot_comp m m' c.1))

theorem HypF.pull_id {p n : ℕ} (x : HypF F p n) : HypF.pull (CoefMap.id F) p n x = x := by
  obtain ⟨c, rfl⟩ := HypF.mk_surjective F p n x
  exact congrArg (HypF.mk F p n) (Subtype.ext (pullTot_id c.1))

theorem HypF.pull_comp (m' : CoefMap τ F' F'') {p n : ℕ} (x : HypF F p n) :
    HypF.pull (m.comp m') p n x = HypF.pull m' p n (HypF.pull m p n x) := by
  obtain ⟨c, rfl⟩ := HypF.mk_surjective F p n x
  exact congrArg (HypF.mk F'' p n) (Subtype.ext (pullTot_comp m m' c.1))

end Pull

end GlobalTheory.HodgeCoh
