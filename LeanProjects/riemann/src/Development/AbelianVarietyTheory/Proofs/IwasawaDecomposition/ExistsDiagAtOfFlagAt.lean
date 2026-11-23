import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsPrincipalMapDifferent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepHoldsLocalTangentFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransitionUniqueAndPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulEqOneOfSubst

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.GradedPieces GlobalTheory.Points GlobalTheory.LieMet

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem inf_le_preimage (q q' : LatChart Z L) (hg : q.g = q'.g) : q.U ⊓ q'.U ≤ q.g ⁻¹ᵁ (q.V ⊓ q'.V) :=
  fun z hz => ⟨q.le hz.1, by rw [hg]; exact q'.le hz.2⟩

def pullInf (q q' : LatChart Z L) (hg : q.g = q'.g) : Γ(B.X, q.V ⊓ q'.V) →+* Γ(Z.X, q.U ⊓ q'.U) :=
  (q.g.appLE _ _ (inf_le_preimage q q' hg)).hom

def crd (q q' : LatChart Z L) (l : Fin q'.n) (j : Fin q.n) : Γ(B.X, q.V ⊓ q'.V) :=
  (q.frame.basis (inf_le_left : q.V ⊓ q'.V ≤ q.V)).repr (GlobalTheory.Twist.resM _ inf_le_right (q'.m l)) j

def crossC (q q' : LatChart Z L) (hg : q.g = q'.g) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (l : Fin q'.n) :
    Γ(Z.X, q.U ⊓ q'.U) :=
  ∑ j, pullInf q q' hg (crd q q' l j) * resG _ inf_le_left (q.c σ i j)

def extMat (q : LatChart Z L) (σ : E →+* ℂ) : GL (Fin q.n) Γ(Z.X, q.U) := (q.ext σ).choose

def extEmb (q : LatChart Z L) (σ : E →+* ℂ) : Fin (Dw.mult σ) ↪ Fin q.n := (q.ext σ).choose_spec.choose

theorem extMat_apply (q : LatChart Z L) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (l : Fin q.n) :
    (q.extMat σ : Matrix (Fin q.n) (Fin q.n) Γ(Z.X, q.U)) (q.extEmb σ i) l = q.c σ i l :=
  (q.ext σ).choose_spec.choose_spec i l

def diagFn (q q' : LatChart Z L) (hg : q.g = q'.g) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) : Γ(Z.X, q.U ⊓ q'.U) :=
  ∑ l, crossC q q' hg σ i l *
    resG _ inf_le_right ((((q'.extMat σ)⁻¹ : GL (Fin q'.n) Γ(Z.X, q'.U)) : Matrix (Fin q'.n) (Fin q'.n) Γ(Z.X, q'.U))
      l (q'.extEmb σ i))

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem tanEv_sum_smul {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ j, a j • s j) = ∑ j, valR x V (a j) * tanEv t hv h (s j) := by
  let f : Γ(GlobalTheory.LieVB.omega t.G, V) →+ k := AddMonoidHom.mk' (tanEv t hv h) (tanEv_add t hv h)
  change f (∑ j, a j • s j) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change tanEv t hv h (a j • s j) = _
  rw [tanEv_smul, valR, dif_pos h]

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem valR_crossC (q q' : LatChart Z L) (hg : q.g = q'.g) {k : Type} [Field k] {x : Sp k ⟶ Z.X}
    {u u' : Vecs Dw (Y Z.i).t k} (hu : q.FrameAt x u) (hu' : q'.FrameAt x u') (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (cf : Fin (Dw.mult σ) → k) (hc : IsCombAtG (Y Z.i).t (x ≫ Z.π) (u' σ) cf (u σ i)) (l : Fin q'.n) :
    valR x (q.U ⊓ q'.U) (crossC q q' hg σ i l) = ∑ b, cf b * valR x q'.U (q'.c σ b l) := by
  obtain ⟨hU, hfl, hco⟩ := hu
  obtain ⟨hU', hfl', hco'⟩ := hu'
  rw [← hg] at hco'
  obtain ⟨τ, mu, hV, htr, hv⟩ := hco
  obtain ⟨τ', mu', hV', htr', hv'⟩ := hco'
  have hx : ⊤ ≤ x ⁻¹ᵁ (q.U ⊓ q'.U) := le_preimage_inf hU hU'
  obtain ⟨a, φ, hφ, hfr, -⟩ := hfl
  obtain ⟨a', φ', hφ', hfr', -⟩ := hfl'
  obtain ⟨y, hy, -⟩ := CommonMod.exists_lift_chart Z hφ
  obtain ⟨rfl, hmu⟩ := GlobalTheory.TransUniq.trans_unique E H Dw Xo p W Y B.i Z.i τ τ' mu mu' q.isMap.1.2.1 htr htr'
  have hmu' : ∀ w : Sp (DualNumber k) ⟶ (Y Z.i).t.G.left, IsTanAtG (Y Z.i).t (x ≫ Z.π) w → w ≫ mu.φ = w ≫ mu'.φ :=
    fun w hw => hmu k y _ (spMap (algebraMap k (DualNumber k))) w (by rw [hw.1, hy])
  have hxτ : (x ≫ Z.π) ≫ τ = (x ≫ q.g) ≫ B.π := by
    rw [Category.assoc, Category.assoc, CommonMod.comp_π_eq q.isMap htr]
  choose v hvt hve hvc using hv σ i
  choose v' hvt' hve' hvc' using hv' σ
  have hcomb : IsCombAtG B.t (x ≫ q.g) v' cf v :=
    StepBasis.isComb_corr mu B.tMap hxτ (fun b => (hfr'.1 σ b).1) hvt'
      (fun b => (hmu' _ (hfr'.1 σ b).1).trans (hve' b).symm) (hfr.1 σ i).1 hvt hve.symm hc
  have hVV : ⊤ ≤ (x ≫ q.g) ⁻¹ᵁ (q.V ⊓ q'.V) := le_preimage_inf hV hV'
  have key := GlobalTheory.LocM.tanEv_comb E H B.X B.t k (x ≫ q.g) _ hVV _ v' hvt' cf v hvt hcomb
    (L.N.incl.app (q.V ⊓ q'.V) (GlobalTheory.Twist.resM _ inf_le_right (q'.m l)))
  have rhs : ∀ b, tanEv B.t (hvt' b) hVV (L.N.incl.app (q.V ⊓ q'.V) (GlobalTheory.Twist.resM _ inf_le_right (q'.m l))) =
      valR x q'.U (q'.c σ b l) := fun b => by
    rw [GlobalTheory.Twist.app_resM, tanEv_resM]
    exact hvc' b l
  have e : GlobalTheory.Twist.resM _ inf_le_right (q'.m l) =
      ∑ j, crd q q' l j • GlobalTheory.Twist.resM _ (inf_le_left : q.V ⊓ q'.V ≤ q.V) (q.m j) := by
    refine ((q.frame.basis inf_le_left).sum_repr _).symm.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [GlobalTheory.VB.IsFrame.basis_apply]
    rfl
  have lhs : tanEv B.t hvt hVV (L.N.incl.app (q.V ⊓ q'.V) (GlobalTheory.Twist.resM _ inf_le_right (q'.m l))) =
      ∑ j, valR (x ≫ q.g) _ (crd q q' l j) * valR x q.U (q.c σ i j) := by
    rw [e, map_sum]
    simp only [Scheme.Modules.Hom.app_smul]
    rw [tanEv_sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [GlobalTheory.Twist.app_resM, tanEv_resM]
    exact congrArg _ (hvc j)
  have hval : valR x (q.U ⊓ q'.U) (crossC q q' hg σ i l) =
      ∑ j, valR (x ≫ q.g) _ (crd q q' l j) * valR x q.U (q.c σ i j) := by
    rw [crossC, valR_eq x _ hx, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← valR_eq x _ hx, ← valR_eq x _ hx, pullInf, valR_appLE x q.g _ hx, valR_res x _ hx]
  rw [hval, ← lhs, key]
  exact Finset.sum_congr rfl fun b _ => by rw [rhs]

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem valR_diagFn (q q' : LatChart Z L) (hg : q.g = q'.g) {k : Type} [Field k] {x : Sp k ⟶ Z.X}
    {u u' : Vecs Dw (Y Z.i).t k} (hu : q.FrameAt x u) (hu' : q'.FrameAt x u') (σ : E →+* ℂ)
    {d : Fin (Dw.mult σ) → k} (hd : DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) d) (i : Fin (Dw.mult σ)) :
    valR x (q.U ⊓ q'.U) (diagFn q q' hg σ i) = d i := by
  obtain ⟨cf, hci, -, hc⟩ := hd i
  have hx : ⊤ ≤ x ⁻¹ᵁ (q.U ⊓ q'.U) := le_preimage_inf hu.1 hu'.1
  have hx' : ⊤ ≤ x ⁻¹ᵁ q'.U := hu'.1
  have hone : ∀ b, ∑ l, valR x q'.U (q'.c σ b l) * valR x q'.U
      ((((q'.extMat σ)⁻¹ : GL (Fin q'.n) Γ(Z.X, q'.U)) : Matrix (Fin q'.n) (Fin q'.n) Γ(Z.X, q'.U)) l (q'.extEmb σ i)) =
        if b = i then 1 else 0 := fun b => by
    simp_rw [← extMat_apply, valR_eq x _ hx', ← map_mul, ← map_sum, ← Matrix.mul_apply]
    rw [Units.mul_inv, Matrix.one_apply]
    simp only [(q'.extEmb σ).injective.eq_iff]
    split_ifs
    · exact map_one _
    · exact map_zero _
  rw [diagFn, valR_eq x _ hx, map_sum]
  simp_rw [map_mul, ← valR_eq x _ hx, valR_crossC q q' hg hu hu' σ i cf hc, valR_res x _ hx, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, hone, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact hci

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B}

theorem exists_diagAt_of_flagAt (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {k : Type} [Field k] {x : Sp k ⟶ Z.X}
    {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u) (h' : Z.FlagAt x u') (σ : E →+* ℂ) :
    ∃ d, DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) d := by
  obtain ⟨_, _, _, hf, _⟩ := id h
  obtain ⟨_, _, _, hf', _⟩ := id h'
  obtain ⟨d, hd⟩ := exists_diag_of_flagAt Z hty h h' σ (fun i => (hf.1 σ i).1) (fun i => (hf'.1 σ i).1)
    (FJ.FlagIndep.linInd_of_frame hf' σ)
  exact ⟨d, (diagAt_iff _ _ d).2 hd⟩

theorem diag_mul_eq_one {k : Type} [Field k] {x : Sp k ⟶ Z.X} {u u' : Vecs Dw (Y Z.i).t k} (h : Z.FlagAt x u)
    (h' : Z.FlagAt x u') {σ : E →+* ℂ} {d d' : Fin (Dw.mult σ) → k}
    (hd : DiagAt (Y Z.i).t (x ≫ Z.π) (u' σ) (u σ) d) (hd' : DiagAt (Y Z.i).t (x ≫ Z.π) (u σ) (u' σ) d')
    (a : Fin (Dw.mult σ)) : d a * d' a = 1 := by
  obtain ⟨_, _, _, hf, _⟩ := h
  obtain ⟨_, _, _, hf', _⟩ := h'
  have t1 := (diagAt_iff (fun i => (hf.1 σ i).1) (fun i => (hf'.1 σ i).1) d').1 hd'
  have t2 := (diagAt_iff (fun i => (hf'.1 σ i).1) (fun i => (hf.1 σ i).1) d).1 hd
  exact congrFun ((t1.trans t2).unique (FJ.FlagIndep.linInd_of_frame hf σ) (Diag.refl _)) a

theorem isUnit_diagFn (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) (q q' : LatChart Z L) (hg : q.g = q'.g)
    (σ : E →+* ℂ) (a : Fin (Dw.mult σ)) : IsUnit (diagFn q q' hg σ a) := by
  refine IsUnit.of_mul_eq_one (resG _ (inf_comm q.U q'.U).le (diagFn q' q hg.symm σ a)) (fn_ext Z fun k _ x h ho => ?_)
  obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x inf_le_left h) ho
  obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x inf_le_right h) ho
  obtain ⟨d, hd⟩ := exists_diagAt_of_flagAt hty hu.2.1 hu'.2.1 σ
  obtain ⟨d', hd'⟩ := exists_diagAt_of_flagAt hty hu'.2.1 hu.2.1 σ
  rw [valR_mul x _ h, valR_res x _ h, valR_one x _ h, valR_diagFn q q' hg hu hu' σ hd a,
    valR_diagFn q' q hg.symm hu' hu σ hd' a]
  exact diag_mul_eq_one hu.2.1 hu'.2.1 hd hd' a

end GlobalTheory.LocM.LatChart

namespace GlobalTheory.LocM.LatChart

theorem existsUnique_isTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z B : Mdl Y i₀) (L : Lat B), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) →
    ∀ (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ), ∃! a : Γ(Z.X, q.U ⊓ q'.U)ˣ, q.IsTr q' e a.val := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z B L hty q q' e
  have hg : q.g = q'.g := MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW Z B q.g q'.g q.isMap q'.isMap
  refine ⟨∏ σ, ∏ i, (isUnit_diagFn hty q q' hg σ i).unit ^ e σ i, fun k _ x u u' d hu hu' hd => ?_, fun b hb => ?_⟩
  · have hx : ⊤ ≤ x ⁻¹ᵁ (q.U ⊓ q'.U) := le_preimage_inf hu.1 hu'.1
    rw [valR_prod_zpow x hx]
    refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [IsUnit.unit_spec, valR_diagFn q q' hg hu hu' σ (hd σ) i]
  · refine Units.ext (fn_ext Z fun k _ x h ho => ?_)
    obtain ⟨u, hu⟩ := q.exists_frameAt (le_preimage_mono x inf_le_left h) ho
    obtain ⟨u', hu'⟩ := q'.exists_frameAt (le_preimage_mono x inf_le_right h) ho
    choose d hd using fun σ => exists_diagAt_of_flagAt hty hu.2.1 hu'.2.1 σ
    rw [hb k x u u' d hu hu' hd, valR_prod_zpow x h]
    refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [IsUnit.unit_spec, valR_diagFn q q' hg hu hu' σ (hd σ) i]

end GlobalTheory.LocM.LatChart
