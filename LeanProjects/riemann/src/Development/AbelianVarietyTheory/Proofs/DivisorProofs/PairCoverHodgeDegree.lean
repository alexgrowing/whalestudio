import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrNormOfTri
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCov.FinLine

open GlobalTheory.ShFam.Pad.Guard GlobalTheory.BcRead.FinPl

def blk {m : ℕ} (i : Fin m) (k : Fin m) : ℕ := min (k + 1 - i) 2

theorem blk_lt {m : ℕ} {i k l : Fin m} : blk i k < blk i l ↔ (k < i ∧ i ≤ l) ∨ (k = i ∧ i < l) := by
  simp only [blk, Fin.lt_def, Fin.le_def, Fin.ext_iff]
  omega

theorem isUnit_mid {S : Type} [CommRing S] {m : ℕ} {N : Matrix (Fin m) (Fin m) S} {i : Fin m}
    (hN : N.BlockTriangular (blk i)) (hd : IsUnit N.det) : IsUnit (N i i) := by
  let _ := Matrix.invertibleOfIsUnitDet N hd
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hN
  have h : (N * N⁻¹) i i = 1 := by rw [N.mul_nonsing_inv hd, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)] at h
  · exact IsUnit.of_mul_eq_one _ h
  · rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hN (blk_lt.2 (.inl ⟨hj, le_rfl⟩)), zero_mul]
    · rw [hI (blk_lt.2 (.inr ⟨rfl, hj⟩)), mul_zero]

section Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem grNorm_of_blk {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X}
    {Λ : Set (Sp (DualNumber C) ⟶ t.G.left)} {m : ℕ} {f u : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}
    (hf : ∀ k, IsTanAtG t x (f k)) (hi : Indep t x f) {M Q Q' : Matrix (Fin m) (Fin m) C}
    (hM : ∀ b, IsCombAtG t x f (fun k => M k b) (u b)) (hQ : ∀ a b, ‖Q a b‖ ≤ 1) (hQ' : ∀ a b, ‖Q' a b‖ ≤ 1)
    (hQQ : Q * Q' = 1) {i : Fin m} (hN : (M * Q).BlockTriangular (blk i)) (hdet : IsUnit (M * Q).det) {δ : C} (hδ : δ ≠ 0)
    (hΛ : ∀ cf w, IsCombAtG t x f cf w →
      ((∃ a : Fin m → C, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG t x u a w) ↔ spMap (epsMul δ) ≫ w ∈ Λ)) :
    grNorm t x Λ f i = (‖δ‖ * ‖(M * Q) i i‖)⁻¹ := by
  have bd : ∀ (A : Matrix (Fin m) (Fin m) C) (a : Fin m → C), (∀ i j, ‖A i j‖ ≤ 1) → (∀ i, ‖a i‖ ≤ 1) →
      ∀ i, ‖A.mulVec a i‖ ≤ 1 := fun A a hA ha i => by
    change ‖∑ j, A i j * a j‖ ≤ 1
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
    rw [norm_mul]; exact mul_le_one₀ (hA _ _) (norm_nonneg _) (ha _)
  have hMd : IsUnit M.det := isUnit_of_mul_isUnit_left (by rwa [Matrix.det_mul] at hdet)
  have hu := fun b => comb_tan hf (hM b)
  have key : ∀ b w, IsCombAtG t x f (δ • (M * Q).mulVec b) w → (w ∈ Λ ↔ ∀ i, ‖b i‖ ≤ 1) := fun cf w h1 => by
    obtain ⟨w', -, hw'⟩ := exists_comb hu (Q.mulVec cf)
    have h2 := tanLinG f hf u M _ w' hM hw'
    have h3 : w = spMap (epsMul δ) ≫ w' := by
      refine comb_unique hf h1 ?_
      convert comb_smul hf h2 δ using 1
      rw [Matrix.mulVec_mulVec]
      rfl
    rw [h3, ← hΛ _ w' h2]
    refine ⟨fun ⟨a, ha, hc⟩ => ?_, fun h => ⟨_, bd Q cf hQ h, hw'⟩⟩
    have h4 := hi _ _ _ (tanLinG f hf u M _ w' hM hc) h2
    have h5 : a = Q.mulVec cf := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hMd) h4
    have h6 : Q'.mulVec a = cf := by
      rw [h5, Matrix.mulVec_mulVec, mul_eq_one_comm.1 hQQ, Matrix.one_mulVec]
    exact h6 ▸ bd Q' a hQ' ha
  have h0 := (isUnit_mid hN hdet).ne_zero
  generalize M * Q = N at key hN hdet h0
  refine IsLeast.csInf_eq ⟨⟨δ • N.mulVec (Pi.single i 1), by simp [hδ, h0], fun j hj => by
    simp [hN (blk_lt.2 (.inr ⟨rfl, hj⟩))], ?_, by simp⟩, ?_⟩
  · obtain ⟨w, -, hw⟩ := exists_comb hf (δ • N.mulVec (Pi.single i 1))
    refine ⟨w, (key _ w hw).2 fun j => ?_, hw⟩
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  · rintro r ⟨cf, h1, h2, ⟨w, hw, hc⟩, rfl⟩
    let _ := Matrix.invertibleOfIsUnitDet N hdet
    have hI := Matrix.blockTriangular_inv_of_blockTriangular hN
    have e : δ • N.mulVec (N⁻¹.mulVec (δ⁻¹ • cf)) = cf := by
      rw [Matrix.mulVec_mulVec, N.mul_nonsing_inv hdet, Matrix.one_mulVec, smul_inv_smul₀ hδ]
    have hb := (key _ w (e.symm ▸ hc)).1 hw i
    have hz : ∀ k, i < k → N⁻¹.mulVec (δ⁻¹ • cf) k = 0 := fun k hk => by
      change ∑ j, N⁻¹ k j * (δ⁻¹ • cf) j = 0
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases lt_trichotomy j i with hj | hj | hj
      · simp [hI (blk_lt.2 (.inl ⟨hj, hk.le⟩))]
      · simp [hI (blk_lt.2 (.inr ⟨hj, hk⟩))]
      · simp [h2 j hj]
    generalize N⁻¹.mulVec (δ⁻¹ • cf) = b at e hb hz
    have e' : cf i = δ * (N i i * b i) := by
      rw [← e]
      change δ * ∑ j, N i j * b j = _
      rw [Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)]
      rcases lt_or_gt_of_ne hj with hj | hj
      · simp [hN (blk_lt.2 (.inl ⟨hj, le_rfl⟩))]
      · simp [hz j hj]
    refine inv_anti₀ (norm_pos_iff.2 h1) ?_
    rw [e', norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) hb) (norm_nonneg _)

theorem blk_of_cols {S K : Type} [CommRing S] [Field K] (ι : S →+* K) (hι : Function.Injective ι)
    {x : Sp S ⟶ X} {m : ℕ} {f u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hf : ∀ k, IsTanAtG t x (f k))
    (hiK : Indep t (spMap ι ≫ x) fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ f k) {M : Matrix (Fin m) (Fin m) S}
    (hM : ∀ b, IsCombAtG t x f (fun k => M k b) (u b))
    {v : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {d : Fin m → K}
    (hv : ∀ i, ∃ cf : Fin m → K, cf i = d i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ f k) cf (v i))
    (A : Matrix (Fin m) (Fin m) S) (i : Fin m) (r : K)
    (h : ∀ a : Fin m → K, ((a = fun c => ι (A c i)) ∨ ∃ k, k < i ∧ a = fun c => ι (A c i + A c k)) →
      ∃ (w : Sp (DualNumber K) ⟶ t.G.left) (cf : Fin m → K),
        IsCombAtG t (spMap ι ≫ x) (fun k => spMap (Formalism.L2.Pj.dualMap ι) ≫ u k) a w ∧
          IsCombAtG t (spMap ι ≫ x) v cf w ∧ cf i = r ∧ ∀ k, i < k → cf k = 0) :
    (M * A).BlockTriangular (blk i) ∧ ι ((M * A) i i) = d i * r := by
  have hfK := fun k => GlobalTheory.FactorDepth.isTanAtG_map t ι (hf k)
  choose T hT1 hT2 hT3 using hv
  let T' : Matrix (Fin m) (Fin m) K := fun j i => T i j
  have hT' : T'.BlockTriangular id := fun j k hk => hT2 k j hk
  have key : ∀ a : Fin m → S, ((a = fun c => A c i) ∨ ∃ k, k < i ∧ a = fun c => A c i + A c k) →
      (∀ k, i < k → ι (M.mulVec a k) = 0) ∧ ι (M.mulVec a i) = d i * r := fun a ha => by
    obtain ⟨w, cf, h1, h2, h3, h4⟩ := h (fun c => ι (a c)) (by
      rcases ha with rfl | ⟨k, hk, rfl⟩
      · exact .inl rfl
      · exact .inr ⟨k, hk, rfl⟩)
    have e1 := hiK _ _ _ (tanLinG _ hfK _ (M.map ι) _ w (fun c => GlobalTheory.LatDRFree.comb_map t ι (hM c)) h1)
      (tanLinG _ hfK v T' cf w hT3 h2)
    have e2 : ∀ k, ι (M.mulVec a k) = T'.mulVec cf k := fun k => by
      rw [← e1]
      exact RingHom.map_mulVec ι M a k
    obtain ⟨e3, e4⟩ := tri_mulVec hT' h4
    exact ⟨fun k hk => (e2 k).trans (e3 k hk), by rw [e2, e4, h3, ← hT1]⟩
  have k₀ := key _ (.inl rfl)
  refine ⟨fun l k hk => hι (Eq.trans ?_ (map_zero ι).symm), k₀.2⟩
  rcases blk_lt.1 hk with ⟨h1, h2⟩ | ⟨rfl, h2⟩
  · have k₁ := key _ (.inr ⟨k, h1, rfl⟩)
    have e : ∀ l, ι (M.mulVec (fun c => A c i + A c k) l) = ι (M.mulVec (fun c => A c i) l) + ι ((M * A) l k) :=
      fun l => by
        rw [← map_add]
        exact congrArg ι (congrFun (M.mulVec_add (fun c => A c i) fun c => A c k) l)
    rcases h2.eq_or_lt with rfl | h2
    · exact left_eq_add.1 (k₀.2.trans (k₁.2.symm.trans (e _))) |>.symm ▸ rfl
    · have := e l
      rwa [k₁.1 l h2, k₀.1 l h2, zero_add, eq_comm] at this
  · exact k₀.1 l h2

end Alg

theorem exists_incl {X : Scheme.{0}} {M : X.Modules} {n : ℕ} (fl : Vert.Flag M n) (k l : Fin (n + 1)) (h : k ≤ l) :
    ∃ g : fl.F k ⟶ fl.F l, g ≫ fl.ι l = fl.ι k := by
  induction l using Fin.induction with
  | zero =>
    obtain rfl : k = 0 := Fin.le_zero_iff.1 h
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ l ih =>
    rcases h.eq_or_lt with rfl | h
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨g, hg⟩ := ih (Fin.le_castSucc_iff.2 h)
      exact ⟨g ≫ fl.step l, by rw [Category.assoc, fl.step_ι, hg]⟩

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (C : FlagCpt Z e)

theorem grNorm_core {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules}
    {τ : E →+* ℂ} {u : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ false u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀} {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin (Dw.mult τ) → Γ(M, V)} (hf : VB.IsFrame f)
    {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V) (A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y₀, W)) (hA : IsUnit A.det)
    (k : Fin (Dw.mult τ)) (r : G.functionField) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (h : ∀ a : Fin (Dw.mult τ) → Γ(Y₀, W), ((a = fun c => A c k) ∨ ∃ l, l < k ∧ a = fun c => A c k + A c l) →
      ∃ (w : Sp (DualNumber G.functionField) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → G.functionField),
        IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
            (fun c => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (a c)) w ∧
          IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (fun l => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ l) cf w ∧
            cf k = r ∧ ∀ l, k < l → cf l = 0)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    {S R : Type} [CommRing S] [CommRing R] {s : Sp S ⟶ G} {ι : S →+* G.functionField} (hι : Function.Injective ι)
    {χ : S →+* AlgebraicClosure F} {σ : R →+* S} {al : R →+* C.Y.Fn} {χ' : R →+* AlgebraicClosure F} {y : Sp R ⟶ C.Y.X}
    {φ₁ : c.F →+* R} (fr : EigFrame Z φ₁ (y ≫ C.π ≫ genι Z)) {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hT : fr.Tri al C.f0 d) (a₁ : spMap χ ≫ s = z) (a₂ : spMap ι ≫ s = FlagCov.genPt G) (a₃ : spMap σ ≫ y = s ≫ πG)
    (a₄ : spMap al ≫ y = genericPt C.Y) (b₁ : χ.comp σ = χ') (b₂ : ι.comp σ = φ.comp al)
    (c₁ : y ≫ C.π ≫ genStr Z = spMap φ₁) (hsW : ⊤ ≤ (s ≫ j) ⁻¹ᵁ W)
    {Ω : Type} [NontriviallyNormedField Ω] [IsUltrametricDist Ω] (io : AlgebraicClosure F →+* Ω)
    (hio : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) (hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V) {δ : Ω} (hδ : δ ≠ 0)
    (Λ : (Sp Ω ⟶ Z.X) → Set (Sp (DualNumber Ω) ⟶ Z.t.G.left))
    (hΛ : ∀ w, IsEigTan Z ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
        (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z) τ w →
      ((∃ a : Fin (Dw.mult τ) → Ω, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z)
          (fun i => spMap (Formalism.L2.Pj.dualMap io) ≫ u V f hf _ (z ≫ jG) hzV i) a w) ↔
        spMap (epsMul δ) ≫ w ∈ Λ (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z)))
    (ψ' : R →+* Ω) (hψ : ∀ a, ψ' a = io (χ' a)) :
    ∃ n : Sˣ, ι n.1 = φ (d τ k : C.Y.Fnˣ) * r ∧
      grNorm Z.t (spMap ψ' ≫ y ≫ C.π ≫ genι Z) (Λ (spMap ψ' ≫ y ≫ C.π ≫ genι Z))
        (fun i => spMap (Formalism.L2.Pj.dualMap ψ') ≫ fr.v τ i) k = (‖δ‖ * ‖io (χ n.1)‖)⁻¹ := by
  have a₅ : spMap χ' ≫ y = z ≫ πG := by rw [← b₁, ← sp_comp', a₃, reassoc_of% a₁]
  have hzW : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hW (Set.mem_univ (spMap ε.O.subtype q))
  have hV : ∀ {K : Type} [CommRing K] (w : Sp K ⟶ G), ⊤ ≤ (w ≫ j) ⁻¹ᵁ W → ⊤ ≤ ((w ≫ jG) ≫ jB) ⁻¹ᵁ V := fun w hy => by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hy (Set.mem_univ q))
  let x := spMap σ ≫ y ≫ C.π ≫ genι Z
  have d₀ : ∀ {T : Scheme.{0}} (g : gen Z ⟶ T),
      (s ≫ jG) ≫ πB ≫ g = spMap σ ≫ y ≫ C.π ≫ g := fun g => by
    rw [Category.assoc, reassoc_of% h₂, reassoc_of% a₃]
  have hub := hu.1 V f hf S (s ≫ jG) (hV s hsW) ((σ.comp φ₁).comp e.toRingHom) (by
    rw [d₀, reassoc_of% c₁, sp_comp', sp_comp])
  rw [d₀, show ((σ.comp φ₁).comp e.toRingHom).comp e.symm.toRingHom = σ.comp φ₁ from RingHom.ext fun a => by simp] at hub
  have nat : ∀ {K : Type} [CommRing K] (ψ : S →+* K) (y : Sp K ⟶ G) (_ : spMap ψ ≫ s = y) (hy),
      u V f hf K (y ≫ jG) hy = fun i => spMap (Formalism.L2.Pj.dualMap ψ) ≫ u V f hf S (s ≫ jG) (hV s hsW) i := by
    rintro K _ ψ _ rfl hy
    exact _root_.funext fun i => hu.2.2 V f hf S K ψ (s ≫ jG) _ hy i
  generalize u V f hf S (s ≫ jG) (hV s hsW) = uS at hub nat
  have hfb := eigBasis_bc fr σ τ
  choose Mc hM using fun i => (hfb.2 _ (hub.1 i)).exists
  choose Mc' hM' using fun i => (hub.2 _ (hfb.1 i)).exists
  have hiK : ∀ {K : Type} [CommRing K] (ψ : S →+* K), IsEigBasis Z ((ψ.comp σ).comp φ₁) (spMap ψ ≫ x) τ fun k =>
      spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (Formalism.L2.Pj.dualMap σ) ≫ fr.v τ k := fun ψ => by
    simp only [x, dual_comp]
    rw [sp_comp']
    exact eigBasis_bc fr _ τ
  have e₁ : FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z = spMap ι ≫ x := by
    rw [← a₂, show x = _ from (d₀ _).symm]; simp only [Category.assoc]
  have hMM : Matrix.of (fun a b => Mc b a) * Matrix.of (fun a b => Mc' b a) = 1 := by
    ext a b
    have := congrFun (indep_of_eig hfb _ _ _ (tanLinG _ (fun k => (hfb.1 k).1) uS (Matrix.of fun a b => Mc b a) _ _ hM (hM' b))
      (isCombAtG_single Z.t _ (fun k => (hfb.1 k).1) b)) a
    rw [Matrix.one_apply, ← Pi.single_apply b (1 : S) a, ← this]
    rfl
  have hdet : IsUnit (Matrix.of (fun a b => Mc b a) * A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).det := by
    rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_det_of_right_inverse hMM).mul (hA.map _)
  obtain ⟨hN, hd⟩ := blk_of_cols ι hι (fun k => (hfb.1 k).1)
    (indep_of_eig (hiK ι)) (M := Matrix.of fun a b => Mc b a) hM
    (v := fun k => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ k) (d := fun k => φ (d τ k : C.Y.Fnˣ))
    (fun i => by
      obtain ⟨cf, g₁, g₂, g₃⟩ := hT.2.2 τ i
      refine ⟨fun k => φ (cf k), congrArg φ g₁, fun k hk => (congrArg φ (g₂ k hk)).trans (map_zero φ), ?_⟩
      have g₄ := GlobalTheory.LatDRFree.comb_map Z.t φ g₃
      simp only [dual_comp, x] at g₄ ⊢
      rw [sp_comp', b₂, ← sp_comp', reassoc_of% a₄]
      exact g₄) (A.map (TangentOrigin.evalPt (s ≫ j) W hsW)) k r (fun a ha => by
      simp only [e₁, nat ι _ a₂, evalPt_eq ι (s ≫ j) (x' := FlagCov.genPt G ≫ j) (by rw [← a₂, Category.assoc]) W hsW] at h
      rcases ha with rfl | ⟨l, hl, rfl⟩
      · exact h _ (.inl rfl)
      · have g := h _ (.inr ⟨l, hl, rfl⟩)
        simp only [map_add (TangentOrigin.evalPt (s ≫ j) W hsW)] at g
        exact g)
  have hun := isUnit_mid hN hdet
  refine ⟨hun.unit, hd, ?_⟩
  let ψ := io.comp χ
  have e₂ : spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z = spMap ψ ≫ x := by
    rw [show x = _ from (d₀ _).symm, ← sp_comp']
    simp only [Category.assoc, reassoc_of% a₁]
  have e₃ : ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom) = (ψ.comp σ).comp φ₁ := by
    have : algebraMap F (AlgebraicClosure F) = (χ'.comp φ₁).comp e.toRingHom := EigLoc.spMap_inj (by
      rw [← sp_comp, ← sp_comp, ← c₁, ← hz, ← C.π_str]
      simp only [Category.assoc, reassoc_of% a₅])
    rw [this, ← b₁]
    refine RingHom.ext fun a => ?_
    change io (χ (σ (φ₁ (e (e.symm a))))) = io (χ (σ (φ₁ a)))
    rw [e.apply_symm_apply]
  have e₄ : ψ' = ψ.comp σ := RingHom.ext fun a => by rw [hψ, ← b₁]; rfl
  rw [e₂, e₃, nat χ z a₁] at hΛ
  simp only [dual_comp] at hΛ
  have hint : ∀ a, ‖ψ (TangentOrigin.evalPt (s ≫ j) W hsW a)‖ ≤ 1 := fun a => by
    have g₁ := evalPt_eq χ (s ≫ j) (x' := z ≫ j) (by rw [reassoc_of% a₁]) W hsW hzW a
    have g₂ := evalPt_eq ε.O.subtype yt hyt.symm W hW hzW a
    exact (hio _).2 (g₁ ▸ g₂ ▸ (TangentOrigin.evalPt yt W hW a).2)
  have mm : (Matrix.of fun a b => Mc b a).map ψ * (A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ =
      (Matrix.of (fun a b => Mc b a) * A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ := Matrix.map_mul.symm
  have hg := grNorm_of_blk (Λ := Λ (spMap ψ ≫ x)) (fun k => ((hiK ψ).1 k).1)
    (indep_of_eig (hiK ψ)) (M := (Matrix.of fun a b => Mc b a).map ψ)
    (Q := (A.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ)
    (Q' := (A⁻¹.map (TangentOrigin.evalPt (s ≫ j) W hsW)).map ψ)
    (fun b => GlobalTheory.LatDRFree.comb_map Z.t ψ (hM b)) (fun _ _ => hint _) (fun _ _ => hint _)
    (by rw [← Matrix.map_mul, ← Matrix.map_mul, A.mul_nonsing_inv hA, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]) (i := k)
    (by rw [mm]; exact fun a b hab => (congrArg ψ (hN hab)).trans (map_zero ψ))
    (by rw [mm, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hdet.map ψ) hδ
    (fun cf w hw => hΛ w (eig_comb (hiK ψ).1 hw))
  rw [mm] at hg
  simp only [dual_comp, x] at hg
  rw [sp_comp', ← e₄] at hg
  exact hg

theorem lnStep_one {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules}
    {τ : E →+* ℂ} {u : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ false u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀} {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin (Dw.mult τ) → Γ(M, V)} (hf : VB.IsFrame f)
    {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V) (A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y₀, W)) (hA : IsUnit A.det)
    (k : Fin (Dw.mult τ)) (r : G.functionField) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (h : ∀ a : Fin (Dw.mult τ) → Γ(Y₀, W), ((a = fun c => A c k) ∨ ∃ l, l < k ∧ a = fun c => A c k + A c l) →
      ∃ (w : Sp (DualNumber G.functionField) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → G.functionField),
        IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
            (fun c => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (a c)) w ∧
          IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (fun l => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ l) cf w ∧
            cf k = r ∧ ∀ l, k < l → cf l = 0)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    {S R : Type} [CommRing S] [CommRing R] {s : Sp S ⟶ G} {ι : S →+* G.functionField} (hι : Function.Injective ι)
    {χ : S →+* AlgebraicClosure F} {σ : R →+* S} {al : R →+* C.Y.Fn} {χ' : R →+* AlgebraicClosure F} {y : Sp R ⟶ C.Y.X}
    {φ₁ : c.F →+* R} (fr : EigFrame Z φ₁ (y ≫ C.π ≫ genι Z)) {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hT : fr.Tri al C.f0 d) (a₁ : spMap χ ≫ s = z) (a₂ : spMap ι ≫ s = FlagCov.genPt G) (a₃ : spMap σ ≫ y = s ≫ πG)
    (a₄ : spMap al ≫ y = genericPt C.Y) (b₁ : χ.comp σ = χ') (b₂ : ι.comp σ = φ.comp al)
    (c₁ : y ≫ C.π ≫ genStr Z = spMap φ₁) (hsW : ⊤ ≤ (s ≫ j) ⁻¹ᵁ W)
    {Ω : Type} [NontriviallyNormedField Ω] [IsUltrametricDist Ω] (io : AlgebraicClosure F →+* Ω)
    (hio : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) {p : ℕ} (hp : 0 < p) (kd : Bool) (hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V) {δ : Ω}
    (hδ : ‖δ‖ = (p : ℝ) ^ (-(if kd = true ∧ τ (H.rt : E) = H.rt0 then vDiff E p else 0)))
    (hΛ : ∀ w, IsEigTan Z ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
        (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z) τ w →
      ((∃ a : Fin (Dw.mult τ) → Ω, (∀ i, ‖a i‖ ≤ 1) ∧ IsCombAtG Z.t (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z)
          (fun i => spMap (Formalism.L2.Pj.dualMap io) ≫ u V f hf _ (z ≫ jG) hzV i) a w) ↔
        spMap (epsMul δ) ≫ w ∈ Pad.lat Z.t p (spMap io ≫ (z ≫ jG) ≫ πB ≫ genι Z) kd))
    (ψ' : R →+* Ω) (hψ : ∀ a, ψ' a = io (χ' a)) :
    ∃ n : Sˣ, ι n.1 = φ (d τ k : C.Y.Fnˣ) * r ∧
      lnStep Z.t (spMap ψ' ≫ y ≫ C.π ≫ genι Z)
        (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ') ≫ fr.v τ i) p kd
          (.inl (τ, k)) = -Real.log ‖io (χ n.1)‖ := by
  have hδ0 : 0 < ‖δ‖ := hδ ▸ Real.rpow_pos_of_pos (by exact_mod_cast hp) _
  obtain ⟨n, k₁, hg⟩ := grNorm_core C hu h₁ h₂ hf hWV A hA k r hx hxV h ε z hz yt hyt hW hι fr hT a₁ a₂ a₃ a₄ b₁ b₂ c₁
    hsW io hio hzV (norm_pos_iff.1 hδ0) (fun x => Pad.lat Z.t p x kd) hΛ ψ' hψ
  refine ⟨n, k₁, ?_⟩
  have hn0 : ‖io (χ n.1)‖ ≠ 0 := norm_ne_zero_iff.2 ((n.isUnit.map χ).map io).ne_zero
  simp only [lnStep, dif_pos k.2]
  refine (congrArg (fun r => Real.log r - _) hg).trans ?_
  rw [Real.log_inv, Real.log_mul hδ0.ne' hn0, hδ, Real.log_rpow (by exact_mod_cast hp)]
  split_ifs <;> ring

theorem lnStep_one_padic {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules}
    {τ : E →+* ℂ} {u : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ false u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀} {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin (Dw.mult τ) → Γ(M, V)} (hf : VB.IsFrame f)
    {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V) (A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y₀, W)) (hA : IsUnit A.det)
    (k : Fin (Dw.mult τ)) (r : G.functionField) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (h : ∀ a : Fin (Dw.mult τ) → Γ(Y₀, W), ((a = fun c => A c k) ∨ ∃ l, l < k ∧ a = fun c => A c k + A c l) →
      ∃ (w : Sp (DualNumber G.functionField) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → G.functionField),
        IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
            (fun c => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (a c)) w ∧
          IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (fun l => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ l) cf w ∧
            cf k = r ∧ ∀ l, k < l → cf l = 0)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W)
    {S R : Type} [CommRing S] [CommRing R] {s : Sp S ⟶ G} {ι : S →+* G.functionField} (hι : Function.Injective ι)
    {χ : S →+* AlgebraicClosure F} {σ : R →+* S} {al : R →+* C.Y.Fn} {χ' : R →+* AlgebraicClosure F} {y : Sp R ⟶ C.Y.X}
    {φ₁ : c.F →+* R} (fr : EigFrame Z φ₁ (y ≫ C.π ≫ genι Z)) {d : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hT : fr.Tri al C.f0 d) (a₁ : spMap χ ≫ s = z) (a₂ : spMap ι ≫ s = FlagCov.genPt G) (a₃ : spMap σ ≫ y = s ≫ πG)
    (a₄ : spMap al ≫ y = genericPt C.Y) (b₁ : χ.comp σ = χ') (b₂ : ι.comp σ = φ.comp al)
    (c₁ : y ≫ C.π ≫ genStr Z = spMap φ₁) (hsW : ⊤ ≤ (s ≫ j) ⁻¹ᵁ W)
    {p : ℕ} {i : Fact p.Prime} (i' : Fact p.Prime) (kd : Bool) (hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (hΛ : haveI := i
      ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-(if kd = true ∧ τ (H.rt : E) = H.rt0 then vDiff E p else 0)) ∧
        ∀ w, IsEigTan Z (((ioOf p ε).comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom)
            (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z) τ w →
          ((∃ a : Fin (Dw.mult τ) → ℂ_[p], (∀ i, ‖a i‖ ≤ 1) ∧
              IsCombAtG Z.t (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z)
                (fun i => spMap (Formalism.L2.Pj.dualMap (ioOf p ε)) ≫ u V f hf _ (z ≫ jG) hzV i) a w) ↔
            spMap (epsMul δ) ≫ w ∈ Pad.lat Z.t p (spMap (ioOf p ε) ≫ (z ≫ jG) ≫ πB ≫ genι Z) kd))
    (hio : ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O) (ψ' : R →+* ℂ_[p]) (hψ : ∀ a, ψ' a = ioOf p ε (χ' a)) :
    ∃ n : Sˣ, ι n.1 = φ (d τ k : C.Y.Fnˣ) * r ∧
      lnStep Z.t (spMap ψ' ≫ y ≫ C.π ≫ genι Z)
        (fun τ i => spMap (Formalism.L2.Pj.dualMap ψ') ≫ fr.v τ i) p kd
          (.inl (τ, k)) = -Real.log ‖ioOf p ε (χ n.1)‖ := by
  obtain rfl : i = i' := rfl
  obtain ⟨δ, hδ, hΛ⟩ := hΛ
  exact lnStep_one C hu h₁ h₂ hf hWV A hA k r hx hxV h ε z hz yt hyt hW hι fr hT a₁ a₂ a₃ a₄ b₁ b₂ c₁ hsW _ hio
    i.out.pos kd hzV hδ hΛ ψ' hψ

theorem symLog_one {Bs Bg Y₀ G : Scheme.{0}} [IsIntegral G] {jB : Bg ⟶ Bs} {πB : Bg ⟶ gen Z} {M : Bs.Modules}
    {τ : E →+* ℂ} {u : FrAssign Z M (Dw.mult τ) jB} (hu : IsLieFrames Z e jB πB M _ τ false u)
    {kind : ℕ → Bool} (hl : IsLieLat Z e jB πB M _ τ kind (fun _ => True) u)
    {π₀ : Y₀ ⟶ Bs} {j : G ⟶ Y₀} {πG : G ⟶ C.Y.X} {φ : C.Y.Fn →+* G.functionField} {jG : G ⟶ Bg}
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ C.Y.X.fromSpecStalk (genericPoint C.Y.X))
    (h₁ : jG ≫ jB = j ≫ π₀) (h₂ : jG ≫ πB = πG ≫ C.π) {V : Bs.Opens} {f : Fin (Dw.mult τ) → Γ(M, V)} (hf : VB.IsFrame f)
    {W : Y₀.Opens} (hWV : W ≤ π₀ ⁻¹ᵁ V) (A : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y₀, W)) (hA : IsUnit A.det)
    (k : Fin (Dw.mult τ)) (r : G.functionField) (hx : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W)
    (hxV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V)
    (h : ∀ a : Fin (Dw.mult τ) → Γ(Y₀, W), ((a = fun c => A c k) ∨ ∃ l, l < k ∧ a = fun c => A c k + A c l) →
      ∃ (w : Sp (DualNumber G.functionField) ⟶ Z.t.G.left) (cf : Fin (Dw.mult τ) → G.functionField),
        IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (u V f hf G.functionField (FlagCov.genPt G ≫ jG) hxV)
            (fun c => TangentOrigin.evalPt (FlagCov.genPt G ≫ j) W hx (a c)) w ∧
          IsCombAtG Z.t (FlagCov.genPt G ≫ jG ≫ πB ≫ genι Z) (fun l => spMap (Formalism.L2.Pj.dualMap φ) ≫ C.f0.v τ l) cf w ∧
            cf k = r ∧ ∀ l, k < l → cf l = 0)
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} (hp : (resP v).Prime) (ε : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ G) (hz : (z ≫ πG) ≫ C.Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (yt : Sp ε.O ⟶ Y₀) (hyt : spMap ε.O.subtype ≫ yt = z ≫ j) (hW : ⊤ ≤ yt ⁻¹ᵁ W) :
    (∀ a : C.Y.X.presheaf.stalk (below (z ≫ πG)), ∃ a' : G.presheaf.stalk (below z),
      algebraMap _ G.functionField a' = φ (algebraMap _ C.Y.X.functionField a) ∧
        (Scheme.stalkClosedPointTo z).hom a' = (Scheme.stalkClosedPointTo (z ≫ πG)).hom a) ∧
    ∃ n : (G.presheaf.stalk (below z))ˣ, algebraMap _ G.functionField n.1 =
        φ ((C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose τ k : C.Y.Fnˣ) * r ∧
      haveI := Fact.mk hp
      LineNorm.symLog C kind (.inl (τ, k)) v ε ⟨z ≫ πG, hz⟩ = (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        -Real.log ‖ioOf (resP v) ε ((Scheme.stalkClosedPointTo z).hom n.1)‖ := by
  obtain ⟨hT, -⟩ := (C.gr_spec (below (z ≫ πG))).choose_spec.choose_spec.choose_spec
  obtain ⟨σ, a₃⟩ : ∃ σ : C.Y.X.presheaf.stalk (below (z ≫ πG)) →+* G.presheaf.stalk (below z),
      spMap σ ≫ stalkPt C.Y (below (z ≫ πG)) = G.fromSpecStalk (below z) ≫ πG :=
    ⟨(πG.stalkMap (below z)).hom, Scheme.SpecMap_stalkMap_fromSpecStalk πG⟩
  have a₁ : spMap (Scheme.stalkClosedPointTo z).hom ≫ G.fromSpecStalk (below z) = z :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) z
  have a₂ : spMap (algebraMap (G.presheaf.stalk (below z)) G.functionField) ≫ G.fromSpecStalk (below z) =
      FlagCov.genPt G :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes (below z))
  have a₄ : spMap (algebraMap (C.Y.X.presheaf.stalk (below (z ≫ πG))) C.Y.X.functionField) ≫
      stalkPt C.Y (below (z ≫ πG)) = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)
  have a₅ : spMap (Scheme.stalkClosedPointTo (z ≫ πG)).hom ≫ stalkPt C.Y (below (z ≫ πG)) = z ≫ πG :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of _) (z ≫ πG)
  have : Mono (stalkPt C.Y (below (z ≫ πG))) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk _))
  have b₁ : (Scheme.stalkClosedPointTo z).hom.comp σ = (Scheme.stalkClosedPointTo (z ≫ πG)).hom :=
    EigLoc.spMap_inj ((cancel_mono (stalkPt C.Y (below (z ≫ πG)))).1
      ((sp_comp' _ _ _).symm.trans <| (congrArg (_ ≫ ·) a₃).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ πG) a₁).trans a₅.symm))
  have b₂ : (algebraMap (G.presheaf.stalk (below z)) G.functionField).comp σ =
      φ.comp (algebraMap (C.Y.X.presheaf.stalk (below (z ≫ πG))) C.Y.X.functionField) :=
    EigLoc.spMap_inj ((cancel_mono (stalkPt C.Y (below (z ≫ πG)))).1
      ((sp_comp' _ _ _).symm.trans <| (congrArg (_ ≫ ·) a₃).trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ πG) a₂).trans <| φs.trans <| (congrArg (_ ≫ ·) a₄.symm).trans (sp_comp' _ _ _)))
  refine ⟨fun a => ⟨σ a, RingHom.congr_fun b₂ a, RingHom.congr_fun b₁ a⟩, ?_⟩
  have c₁ : stalkPt C.Y (below (z ≫ πG)) ≫ C.π ≫ genStr Z = spMap (C.gr_spec (below (z ≫ πG))).choose :=
    VarFlagSpec.eq_spMap_of_comp (IsFractionRing.injective _ C.Y.X.functionField)
      ((Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) a₄).trans <| (VarFlagSpec.genericPt_genStr C).trans <|
        congrArg spMap hT.2.1)
  have hzW : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hW (Set.mem_univ (spMap ε.O.subtype q))
  have hsW : ⊤ ≤ (G.fromSpecStalk (below z) ≫ j) ⁻¹ᵁ W := le_pre (R := G.presheaf.stalk (below z)) _ _
    ((congrArg (fun q => j q ∈ W) Scheme.fromSpecStalk_closedPoint).mpr
      (hzW (Set.mem_univ (IsLocalRing.closedPoint _))))
  have hzV : ⊤ ≤ ((z ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hzW (Set.mem_univ q))
  obtain ⟨hp', hio, -⟩ := ioOf_spec F v ε
  obtain rfl : hp = hp' := rfl
  have hΛ := hl v trivial hp ε (z ≫ jG) (yt ≫ π₀) (by
      rw [Category.assoc, reassoc_of% h₂, C.π_str, ← hz, Category.assoc])
    (by rw [reassoc_of% hyt, Category.assoc, h₁]) V f hf (fun q _ => hWV (hW (Set.mem_univ q))) hzV
  obtain ⟨n, k₁, k₂⟩ := lnStep_one_padic C hu h₁ h₂ hf hWV A hA k r hx hxV h ε z hz yt hyt hW
    (IsFractionRing.injective (G.presheaf.stalk (below z)) G.functionField) _ hT a₁ a₂ a₃ a₄ b₁ b₂ c₁ hsW
    (Fact.mk hp) _ hzV hΛ hio _ (fun _ => RingHom.comp_apply _ _ _)
  exact ⟨n, k₁, (symLog_eq C hp ε _ kind _).trans (congrArg _ k₂)⟩

end Free

theorem lg_line_eq : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j)) (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    (Y X Gs : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    IsArithVar (ρ ≫ π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG →
    ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : VMetric q M (O.S.Dw.mult σ)) (HM : hM.IsCInf)
      (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB), IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t →
    IsLieLat O.s.T.Z O.κ.e jB πB M _ σ (ArIn.ind ∅) (fun _ => True) t →
    ∀ (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
      (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM.isVB jB πB t π ρ F j φ jG i r →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (O.var c))
      (z : Sp (AlgebraicClosure D.what₂.LL) ⟶ Gs) (yt : Sp e.O ⟶ X) (ch : ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).ι),
      z ≫ πG = y.1 → spMap e.O.subtype ≫ yt = z ≫ j → ⊤ ≤ yt ⁻¹ᵁ (VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.U (ch PUnit.unit) →
        ((1 : ℕ) : ℝ) * (lineAdl O R c (.inl (σ, (i : ℕ))) 1).lg v e y =
          Real.log (e.w (valAt z (φ (genAt (lineAdl O R c (.inl (σ, (i : ℕ))) 1).D (below y.1)) ^ 1 * (r ch : Gs.functionField)))) := by
  intro _ _ _ D O _ R _ c Bs _ q _ _ Bg jB πB Gm Y X G _ _ _ π ρ j πG φ jG _ _ hc σ M h H u hu hl fl i r hs v e
    y z yt ch hz hyt hU
  obtain ⟨-, -, -, -, -, -, -, φs, h₁, h₂⟩ := hc
  obtain ⟨hp, -⟩ := ioOf_spec _ v e
  have := h.isVB.isQuasicoherent
  have := (h.isVB.pullback π).isQuasicoherent
  obtain ⟨y, hy⟩ := y
  obtain rfl : z ≫ πG = y := hz
  have hch : ∃ ck : ∀ k, Chart (fl.gr k) 1, ck i = ch PUnit.unit ∧
      ∀ k, yt (IsLocalRing.closedPoint e.O) ∈ (ck k).U := by
    choose U f hx hf using fun k => fl.isVB_gr k (yt (IsLocalRing.closedPoint e.O))
    obtain ⟨c₀, hc₀, hU'⟩ : ∃ c₀ : Chart (fl.gr i) 1, c₀ = ch PUnit.unit ∧
      yt (IsLocalRing.closedPoint e.O) ∈ c₀.U := ⟨_, rfl, hU (Set.mem_univ _)⟩
    refine ⟨Function.update (fun k => ⟨U k, f k, hf k⟩) i c₀, (Function.update_self ..).trans hc₀, fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact hU'
    · rw [Function.update_of_ne hk]
      exact hx k
  obtain ⟨ck, hck, hx⟩ := hch
  obtain ⟨V, f, hV, hf⟩ := h.isVB (π (ρ (yt (IsLocalRing.closedPoint e.O))))
  obtain ⟨W, hxW, hWV, hW, t, ht, hfr⟩ := exists_lifts fl _ ck hx (ρ ⁻¹ᵁ (π ⁻¹ᵁ V)) hV
  have hyW := le_pre yt W hxW
  have hgW : ⊤ ≤ (FlagCov.genPt G ≫ j) ⁻¹ᵁ W := le_pre (R := G.functionField) _ _ (by
    have h0 : ⊤ ≤ (z ≫ j) ⁻¹ᵁ W := hyt ▸ fun q _ => hyW (Set.mem_univ (spMap e.O.subtype q))
    have h1 : FlagCov.genPt G (IsLocalRing.closedPoint _) = genericPoint G := Scheme.fromSpecStalk_closedPoint
    exact (congrArg (fun q => j q ∈ W) h1).mpr ((genericPoint_specializes (below z)).mem_open (j ⁻¹ᵁ W).isOpen
      (h0 (Set.mem_univ (IsLocalRing.closedPoint _)))))
  have hgV : ⊤ ≤ ((FlagCov.genPt G ≫ jG) ≫ jB) ⁻¹ᵁ V := by
    rw [Category.assoc, h₁, ← Category.assoc]
    exact fun q _ => hWV (hgW (Set.mem_univ q))
  have hA : IsUnit (Matrix.det (Matrix.of fun b k =>
      (((hf.pullback π).pullback ρ).basis hWV).repr ((fl.ι k.succ).app W (t k)) b)) := by
    have := (((hf.pullback π).pullback ρ).basis hWV).isUnit_det (hfr.basis le_rfl)
    rw [Module.Basis.det_apply] at this
    convert this using 2
    ext b k
    rw [Module.Basis.toMatrix_apply, IsFrame.basis_apply, Twist.resM_self]
    rfl
  obtain ⟨k₁, n, k₂, k₃⟩ := symLog_one (O.Φ.C c) hu hl (π₀ := ρ ≫ π) φs h₁ h₂ hf hWV _ hA i
    (((r fun _ => ck i)⁻¹ : G.functionFieldˣ) : G.functionField) hgW hgV (fun a ha => by
      rcases ha with rfl | ⟨l, hl, rfl⟩
      · exact hs (fun _ => ck i) V f hf W (hW i) hWV (t i) (ht i) hgW hgV
      · obtain ⟨g, hg⟩ := exists_incl fl l.succ i.castSucc (Fin.succ_le_castSucc_iff.2 hl)
        have g₁ : (fl.π i).app W ((g ≫ fl.step i).app W (t l)) = 0 := by
          rw [QCoh.app_app, Category.assoc, show fl.step i ≫ fl.π i = 0 from Limits.cokernel.condition _, Limits.comp_zero]
          rfl
        have g₂ : (fl.ι i.succ).app W (t i + (g ≫ fl.step i).app W (t l)) =
            (fl.ι i.succ).app W (t i) + (fl.ι l.succ).app W (t l) := by
          rw [map_add, QCoh.app_app, Category.assoc, fl.step_ι, hg]
        have g₃ := hs (fun _ => ck i) V f hf W (hW i) hWV (t i + (g ≫ fl.step i).app W (t l))
          (by rw [map_add, g₁, add_zero]; exact ht i) hgW hgV
        rw [g₂, map_add] at g₃
        exact g₃) hp e z hy yt hyt hyW
  have hri : (r fun _ => ck i) = r ch := congrArg _ (_root_.funext fun _ => hck)
  rw [Nat.cast_one, one_mul, ← hri]
  exact lgOf_single (O.Φ.C c) hp e z hy _ _ _ i 1 (.inl rfl) _ rfl _ k₁ (zpow_neg_one _).symm n k₂ k₃

end GlobalTheory.PairCov.FinLine

end
