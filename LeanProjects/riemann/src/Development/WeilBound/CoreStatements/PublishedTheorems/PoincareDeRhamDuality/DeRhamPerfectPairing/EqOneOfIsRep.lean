import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTriviali
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

open GlobalTheory.Points GlobalTheory.CechKS.PrismDlog

section General

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (s : Y ⟶ Sp R)

theorem le_of_pts {U V : Y.Opens} (h : ∀ P : Pt s, P.In U → P.In V) : U ≤ V := by
  intro y hy
  obtain ⟨U', hU', hy', hsub⟩ := exists_isAffineOpen_mem_and_subset (U := U) hy
  have hP : (Pt.aff s ⟨U', hU'⟩).In U' := hU'.fromSpec_preimage_self.ge
  have h2 := h _ (hP.mono hsub)
  have : y ∈ Set.range hU'.fromSpec := by rw [hU'.range_fromSpec]; exact hy'
  obtain ⟨z, rfl⟩ := this
  exact h2 (Set.mem_univ z)

theorem valR_hom {P Q : Pt s} (φ : P.Hom Q) {U : Y.Opens} (h : P.In U) (f : Γ(Y, U)) :
    valR Q.x U f = φ.ρ (valR P.x U f) := by
  rw [← φ.pt, valR_spMap_comp _ _ _ h]; rfl

theorem exists_secA {J : Type} (W : J → Y.Opens) (hW : ⨆ k, W k = ⊤) (U : Y.Opens) (a : J → PtFn s)
    (h₁ : ∀ k k' (P : Pt s), P.In U → P.In (W k) → P.In (W k') → a k P = a k' P)
    (h₂ : ∀ k, IsNat (U ⊓ W k) (a k)) :
    ∃ f : Γ(Y, U), ∀ k (P : Pt s), P.In U → P.In (W k) → valR P.x U f = a k P := by
  classical
  let F : PtFn s := fun P ↦ if h : ∃ k, P.In (W k) then a h.choose P else 0
  have hF : ∀ k (P : Pt s), P.In U → P.In (W k) → F P = a k P := fun k P hU hk ↦ by
    have h : ∃ k, P.In (W k) := ⟨k, hk⟩
    simp only [F, dif_pos h]
    exact h₁ _ _ P hU h.choose_spec hk
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover R Y s J (fun k ↦ U ⊓ W k) U (fun k ↦ inf_le_left)
    (by rw [← inf_iSup_eq, hW, inf_top_eq]) F fun k P Q φ hP ↦ by
      rw [hF k P (hP.mono inf_le_left) (hP.mono inf_le_right),
        hF k Q ((hP.map φ).mono inf_le_left) ((hP.map φ).mono inf_le_right)]
      exact h₂ k P Q φ hP
  exact ⟨f, fun k P hU hk ↦ (hf k P (hU.inf hk)).symm.trans (hF k P hU hk)⟩

theorem valR_mul_inv {C : Type} [CommRing C] (x : Sp C ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    valR x U u.val * valR x U u⁻¹.val = 1 := by
  rw [← valR_mul _ _ h, Units.mul_inv, valR_one _ _ h]

theorem triv_of_local {M : LB Y} (hM : M.IsLB) {J : Type} (W : J → Y.Opens) (hW : ⨆ k, W k = ⊤) (c : J → M.ι)
    (hc : ∀ k, W k ≤ M.U (c k)) (u : ∀ k, Γ(Y, W k)ˣ)
    (hu : ∀ k k' (P : Pt s), P.In (W k) → P.In (W k') →
      valR P.x _ (u k).val = valR P.x _ (M.g (c k) (c k')).val * valR P.x _ (u k').val) : GlobalTheory.AbLaw.Triv M := by
  let a : M.ι → J → PtFn s := fun i k P ↦ valR P.x _ (M.g i (c k)).val * valR P.x _ (u k).val
  let a' : M.ι → J → PtFn s := fun i k P ↦ valR P.x _ (M.g i (c k))⁻¹.val * valR P.x _ (u k)⁻¹.val
  have e₁ : ∀ i k k' (P : Pt s), P.In (M.U i) → P.In (W k) → P.In (W k') → a i k P = a i k' P := by
    intro i k k' P hi hk hk'
    simp only [a]
    rw [hu k k' P hk hk', ← _root_.mul_assoc,
      valR_cocycle M hM P.x i (c k) (c k') ((hi.inf (hk.mono (hc k))).inf (hk'.mono (hc k')))]
  have e₂ : ∀ i k (P : Pt s), P.In (M.U i) → P.In (W k) → a i k P * a' i k P = 1 := by
    intro i k P hi hk
    simp only [a, a']
    rw [_root_.mul_mul_mul_comm, valR_mul_inv _ _ (hi.inf (hk.mono (hc k))), valR_mul_inv _ _ hk, _root_.mul_one]
  have e₃ : ∀ i k k' (P : Pt s), P.In (M.U i) → P.In (W k) → P.In (W k') → a' i k P = a' i k' P := by
    intro i k k' P hi hk hk'
    have h1 := e₂ i k P hi hk
    have h2 := e₂ i k' P hi hk'
    rw [← e₁ i k k' P hi hk hk'] at h2
    linear_combination (a' i k' P) * h1 - (a' i k P) * h2
  have n₁ : ∀ i k, IsNat (M.U i ⊓ W k) (a i k) := fun i k P Q φ hP ↦ by
    simp only [a]
    rw [map_mul, valR_hom s φ (hP.mono inf_le_right), valR_hom s φ (hP.mono (inf_le_inf_left _ (hc k)))]
  have n₂ : ∀ i k, IsNat (M.U i ⊓ W k) (a' i k) := fun i k P Q φ hP ↦ by
    simp only [a']
    rw [map_mul, valR_hom s φ (hP.mono inf_le_right), valR_hom s φ (hP.mono (inf_le_inf_left _ (hc k)))]
  choose f hf using fun i ↦ exists_secA s W hW (M.U i) (a i) (e₁ i) (n₁ i)
  choose f' hf' using fun i ↦ exists_secA s W hW (M.U i) (a' i) (e₃ i) (n₂ i)
  have hff : ∀ i, f i * f' i = 1 := fun i ↦
    eq_of_valR_eq_on_cover s W hW _ _ _ fun P k hi hk ↦ by
      rw [valR_mul _ _ hi, valR_one _ _ hi, hf i k P hi hk, hf' i k P hi hk, e₂ i k P hi hk]
  refine ⟨⟨fun i ↦ Units.mkOfMulEqOne _ _ (hff i)⟩, fun i j ↦ Units.ext ?_⟩
  refine eq_of_valR_eq_on_cover s W hW _ _ _ fun P k hij hk ↦ ?_
  have hi : P.In (M.U i) := hij.mono inf_le_left
  have hj : P.In (M.U j) := hij.mono inf_le_right
  rw [Units.val_mul, valR_mul _ _ hij]
  change valR P.x _ ((Y.presheaf.map (homOfLE inf_le_left).op).hom (f i)) =
    _ * valR P.x _ ((Y.presheaf.map (homOfLE inf_le_right).op).hom (f j))
  rw [valR_res _ _ hij, valR_res _ _ hij, hf i k P hi hk, hf j k P hj hk]
  simp only [a]
  rw [← _root_.mul_assoc, valR_cocycle M hM P.x i j (c k) (hij.inf (hk.mono (hc k)))]

end General

def evEps {B : Type} [CommRing B] (e : B) (he : e * e = 0) : DualNumber B →+* B where
  toFun c := c.fst + c.snd * e
  map_one' := by simp
  map_mul' x y := by
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    linear_combination (-(x.snd * y.snd)) * he
  map_zero' := by simp
  map_add' x y := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add]; ring

section Tr

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

@[reducible] def sndPt (P : Pt (epsR K ⊗ A).hom) : GPt A where
  B := P.B
  x := P.x ≫ (snd (epsR K) A).left
  w := by rw [Category.comp_id, Category.assoc, Over.w, P.w]

def fstHomPt (P : Pt (epsR K ⊗ A).hom) : DualNumber K →+* P.B :=
  (Spec.preimage (P.x ≫ (fst (epsR K) A).left : Sp P.B ⟶ Sp (DualNumber K))).hom

theorem spMap_fstHomPt (P : Pt (epsR K ⊗ A).hom) : spMap (fstHomPt P) = P.x ≫ (fst (epsR K) A).left :=
  Spec.map_preimage _

theorem fstHomPt_sq (P : Pt (epsR K ⊗ A).hom) : fstHomPt P DualNumber.eps * fstHomPt P DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem fstHomPt_comp (P : Pt (epsR K ⊗ A).hom) :
    (fstHomPt P).comp (algebraMap K (DualNumber K)) = algebraMap K P.B := by
  have e : spMap ((fstHomPt P).comp (algebraMap K (DualNumber K))) = spMap (algebraMap K P.B) := by
    rw [GlobalTheory.Cris.spMap_comp, spMap_fstHomPt, ← P.w, Category.assoc]
    exact congrArg (P.x ≫ ·) (Over.w (fst (epsR K) A))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem pt_transl [IsCommMonObj A] (v : epsR K ⟶ A) (P : Pt (epsR K ⊗ A).hom) :
    P.x ≫ (lift (fst (epsR K) A ≫ v) (snd (epsR K) A) ≫ μ[A]).left =
      spMap (evEps _ (fstHomPt_sq P)) ≫ (sndPt P).trx v := by
  obtain ⟨x', v', hx', hv', hw⟩ := (sndPt P).isTransl_trx v
  have i1 : (evEps _ (fstHomPt_sq P)).comp (algebraMap P.B (DualNumber P.B)) = RingHom.id _ :=
    RingHom.ext fun b ↦ by simp [evEps, TrivSqZeroExt.algebraMap_eq_inl]
  have i2 : (evEps _ (fstHomPt_sq P)).comp (dualMap (algebraMap K P.B)) = fstHomPt P :=
    RingHom.ext fun c ↦ by
      have h1 : ∀ k, algebraMap K P.B k = fstHomPt P (algebraMap K _ k) := fun k ↦
        (RingHom.congr_fun (fstHomPt_comp P) k).symm
      have h2 : c = algebraMap K _ c.fst + algebraMap K _ c.snd * DualNumber.eps := by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      conv_rhs => rw [h2, map_add, map_mul, ← h1, ← h1]
      simp [evEps, dualMap, Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl]
  let y : Over.mk (spMap (algebraMap K P.B)) ⟶ epsR K ⊗ A := Over.homMk P.x P.w
  let j : Over.mk (spMap (algebraMap K P.B)) ⟶
      Over.mk (spMap ((algebraMap P.B (DualNumber P.B)).comp (algebraMap K P.B))) :=
    Over.homMk (spMap (evEps _ (fstHomPt_sq P))) (by
      change spMap _ ≫ spMap _ = spMap _
      rw [← GlobalTheory.Cris.spMap_comp, ← RingHom.comp_assoc, i1, RingHom.id_comp])
  have e1 : j ≫ x' = y ≫ snd (epsR K) A := by
    apply Over.OverMorphism.ext
    change spMap _ ≫ x'.left = P.x ≫ _
    rw [hx', ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, i1, GlobalTheory.Cris.spMap_id, Category.id_comp]
  have e2 : j ≫ v' = y ≫ fst (epsR K) A ≫ v := by
    apply Over.OverMorphism.ext
    change spMap _ ≫ v'.left = P.x ≫ (fst (epsR K) A).left ≫ v.left
    rw [hv', ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, i2, spMap_fstHomPt, Category.assoc]
  have e3 : y ≫ ((fst (epsR K) A ≫ v) * snd (epsR K) A) = j ≫ (x' * v') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2, _root_.mul_comm]
  rw [← hw]
  exact congrArg Over.Hom.left e3

theorem triv_translDiff [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) {v : epsR K ⟶ A} (hv : IsTangent v)
    {J : Type} (V : J → A.left.Opens) (hV : ⨆ j, V j = ⊤) (τ : J → L.ι) (hτ : ∀ j, V j ≤ L.U (τ j))
    (n : ∀ j, Γ(A.left, V j))
    (hn : ∀ j j' (P : GPt A), P.In (V j) → P.In (V j') →
      valR P.x _ (n j) - valR P.x _ (n j') = dlog L v (τ j) (τ j') P) :
    GlobalTheory.AbLaw.Triv (Out.translDiff A L v) := by
  let a := (lift (fst (epsR K) A ≫ v) (snd (epsR K) A) ≫ μ[A]).left
  let b := (snd (epsR K) A).left
  let p : (epsR K ⊗ A).left ⟶ Sp (DualNumber K) := (fst (epsR K) A).left
  have hab : ∀ (U : A.left.Opens) (P : Pt (epsR K ⊗ A).hom), P.In (b ⁻¹ᵁ U) → ⊤ ≤ (P.x ≫ a) ⁻¹ᵁ U := by
    intro U P hP
    have h1 : (sndPt P).In U := hP
    have h2 : ⊤ ≤ ((sndPt P).trx v) ⁻¹ᵁ U := h1.tr hv
    simp only [a]
    rw [pt_transl]
    exact fun z _ ↦ h2 (Set.mem_univ _)
  have hle : ∀ U : A.left.Opens, b ⁻¹ᵁ U ≤ a ⁻¹ᵁ U := fun U ↦ le_of_pts (epsR K ⊗ A).hom (hab U)
  have hsq : ∀ U, constFn p U DualNumber.eps * constFn p U DualNumber.eps = 0 := fun U ↦ by
    simp only [constFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  refine triv_of_local (epsR K ⊗ A).hom (LB.isLB_linComb hL _ _) (fun j ↦ b ⁻¹ᵁ V j)
    (by rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]) (fun j _ ↦ τ j) ?_
    (fun j ↦ Units.mkOfMulEqOne (1 + constFn p _ DualNumber.eps * (b.app (V j)).hom (n j))
      (1 - constFn p _ DualNumber.eps * (b.app (V j)).hom (n j))
      (by linear_combination (-((b.app (V j)).hom (n j)) ^ 2) * hsq (b ⁻¹ᵁ V j))) ?_
  · intro j y hy
    refine Set.mem_iInter.2 fun k ↦ ?_
    fin_cases k
    · exact hle _ (hτ j hy)
    · exact hτ j hy
  · intro j j' P hj hj'
    have hu : ∀ j, P.In (b ⁻¹ᵁ V j) → valR P.x (b ⁻¹ᵁ V j)
        (1 + constFn p _ DualNumber.eps * (b.app (V j)).hom (n j)) =
        1 + fstHomPt P DualNumber.eps * valR (sndPt P).x _ (n j) := fun j hj ↦ by
      rw [valR_add _ _ hj, valR_mul _ _ hj, valR_one _ _ hj, valR_constFn _ _ _ hj, ← valR_comp]
      rfl
    have q : (sndPt P).In (V j) := hj
    have q' : (sndPt P).In (V j') := hj'
    have qq : (sndPt P).In (L.U (τ j) ⊓ L.U (τ j')) := (q.mono (hτ j)).inf (q'.mono (hτ j'))
    have hw : ∀ j, b ⁻¹ᵁ V j ≤ LB.wchart L ![a, b] fun _ ↦ τ j := by
      intro j y hy
      refine Set.mem_iInter.2 fun k ↦ ?_
      fin_cases k
      · exact hle _ (hτ j hy)
      · exact hτ j hy
    have hPw : P.In (LB.wchart L ![a, b] (fun _ ↦ τ j) ⊓ LB.wchart L ![a, b] fun _ ↦ τ j') :=
      (hj.mono (hw j)).inf (hj'.mono (hw j'))
    have la : LB.wchart L ![a, b] (fun _ ↦ τ j) ⊓ LB.wchart L ![a, b] (fun _ ↦ τ j') ≤
        a ⁻¹ᵁ (L.U (τ j) ⊓ L.U (τ j')) :=
      le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] _ 0)) (inf_le_right.trans (LB.wchart_le L ![a, b] _ 0))
    have lb : LB.wchart L ![a, b] (fun _ ↦ τ j) ⊓ LB.wchart L ![a, b] (fun _ ↦ τ j') ≤
        b ⁻¹ᵁ (L.U (τ j) ⊓ L.U (τ j')) :=
      le_inf (inf_le_left.trans (LB.wchart_le L ![a, b] _ 1)) (inf_le_right.trans (LB.wchart_le L ![a, b] _ 1))
    have eg : (LB.LinComb L ![a, b] ![1, -1]).g (fun _ ↦ τ j) (fun _ ↦ τ j') =
        res la (pullU a _ (L.g (τ j) (τ j'))) * res lb (pullU b _ (L.g (τ j) (τ j'))⁻¹) := by
      simp only [LB.LinComb, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, map_inv]
      rfl
    have ev : valR P.x _ ((LB.LinComb L ![a, b] ![1, -1]).g (fun _ ↦ τ j) (fun _ ↦ τ j')).val =
        valR (P.x ≫ a) _ (L.g (τ j) (τ j')).val * valR (sndPt P).x _ (L.g (τ j) (τ j'))⁻¹.val := by
      rw [eg, Units.val_mul]
      refine (valR_mul _ _ hPw _ _).trans (congrArg₂ (· * ·) ?_ ?_)
      · exact (valR_res _ la hPw _).trans (valR_comp _ _ _ _).symm
      · exact (valR_res _ lb hPw _).trans (valR_comp _ _ _ _).symm
    have et : valR (P.x ≫ a) _ (L.g (τ j) (τ j')).val = valR (sndPt P).x _ (L.g (τ j) (τ j')).val +
        (valR ((sndPt P).trx v) _ (L.g (τ j) (τ j')).val).snd * fstHomPt P DualNumber.eps := by
      simp only [a]
      rw [pt_transl, valR_spMap_comp _ _ _ (qq.tr hv), ← fst_valR_trx (sndPt P) hv _ qq]
      rfl
    have h1 := valR_mul_inv (sndPt P).x _ qq (L.g (τ j) (τ j'))
    have h2 := hn j j' (sndPt P) q q'
    have h3 := fstHomPt_sq P
    refine (hu j hj).trans (Eq.trans ?_ (congrArg₂ (· * ·) ev (hu j' hj')).symm)
    rw [et]
    simp only [dlog] at h2
    generalize valR (sndPt P).x _ (L.g (τ j) (τ j')).val = g at *
    generalize valR (sndPt P).x _ (L.g (τ j) (τ j'))⁻¹.val = g' at *
    generalize (valR ((sndPt P).trx v) _ (L.g (τ j) (τ j')).val).snd = w at *
    generalize valR (sndPt P).x _ (n j) = m at *
    generalize valR (sndPt P).x _ (n j') = m' at *
    generalize fstHomPt P DualNumber.eps = e at *
    linear_combination (-(1 + e * m')) * h1 + e * h2 - (w * g' * m') * h3

theorem eq_one_of_isRep [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) {v : epsR K ⟶ A}
    (hv : IsTangent v) {J : Type} (V : J → A.left.Opens) (hV : ⨆ j, V j = ⊤) (τ : J → L.ι)
    (hτ : ∀ j, V j ≤ L.U (τ j)) (c : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hc : IsRep V c fun j j' ↦ dlog L v (τ j) (τ j')) (hF : H1.mk _ c ∈ F1 (A.hom ≫ 𝟙 (Sp K))) : v = 1 := by
  rw [hodgeFiltration_eq_range] at hF
  obtain ⟨ω, hω⟩ := hF
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hω.symm
  obtain ⟨G, h1, h2⟩ := hc
  have hg' : ∀ (P Q : GPt A) (φ : P.Hom Q), GlobalTheory.Cris.ev c φ.triv = g Q.triv - φ.ρ (g P.triv) := fun P Q φ ↦ by
    have e := congrFun (congrFun (congrFun hg P.triv) Q.triv) φ.triv
    have z : ω.1.1 P.triv Q.triv φ.triv = 0 := ω.2 φ.triv rfl rfl
    have key : ∀ x y t : Q.B, x = y - t → t = 0 → y = x := fun x y t a b ↦ by rw [a, b, sub_zero]
    exact key _ _ _ e z
  have ex : ∀ j, ∃ n : Γ(A.left, V j), ∀ P : GPt A, P.In (V j) → G j P - g P.triv = valR P.x _ n := fun j ↦ by
    obtain ⟨n, hn⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K _ (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ V j) (V j) (fun _ ↦ le_rfl)
      (le_iSup (fun _ : Unit ↦ V j) ()) (fun P ↦ G j P - g P.triv) fun _ P Q φ hP ↦ by
        have a := h1 j P Q φ hP
        rw [hg'] at a
        have key : ∀ x y z t : Q.B, x - y = z - t → z - x = t - y := fun x y z t h ↦ by linear_combination -h
        exact (key _ _ _ _ a).trans (map_sub φ.ρ _ _).symm
    exact ⟨n, hn ()⟩
  choose n hn using ex
  have ht := triv_translDiff hL hv V hV τ hτ n fun j j' P hj hj' ↦ by
    rw [← hn j P hj, ← hn j' P hj', sub_sub_sub_cancel_right]
    exact h2 j j' P hj hj'
  have hD : (Out.translDiff A L v).IsLB := LB.isLB_linComb hL _ _
  refine hK (DualNumber K) _ v fun p ↦ ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, (cls_eq_zero_iff hD).2 ht, map_zero]

end Tr

end CrystallinePoints.Pd
