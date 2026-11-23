import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMapUnique

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.GrCl.Annih

theorem exists_trans {X : Scheme.{0}} {F : X.Modules} {V₁ V₂ : X.Opens} {n₁ n₂ : ℕ} {m₁ : Fin n₁ → Γ(F, V₁)}
    {m₂ : Fin n₂ → Γ(F, V₂)} (h₁ : VB.IsFrame m₁) (h₂ : VB.IsFrame m₂) :
    ∃ (T : Matrix (Fin n₁) (Fin n₂) Γ(X, V₁ ⊓ V₂)) (T' : Matrix (Fin n₂) (Fin n₁) Γ(X, V₁ ⊓ V₂)),
      T * T' = 1 ∧ T' * T = 1 ∧ ∀ l, resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) (m₁ l) =
        ∑ i, T l i • resM F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (m₂ i) := by
  let b₁ := h₁.basis (inf_le_left : V₁ ⊓ V₂ ≤ V₁)
  let b₂ := h₂.basis (inf_le_right : V₁ ⊓ V₂ ≤ V₂)
  refine ⟨(b₂.toMatrix b₁).transpose, (b₁.toMatrix b₂).transpose, ?_, ?_, fun l => ?_⟩
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · have := b₂.sum_toMatrix_smul_self b₁ l
    simp only [b₁, b₂, VB.IsFrame.basis_apply] at this
    exact this.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem tanEv_trans {X : Scheme.{0}} (t : SAB H X) {k : Type} [CommRing k] {x : Sp k ⟶ X}
    {v : Sp (DualNumber k) ⟶ t.G.left} (hv : IsTanAtG t x v) {F : X.Modules} (θ : F ⟶ GlobalTheory.LieVB.omega t.G)
    {V₁ V₂ : X.Opens} {n : ℕ} {s : Γ(F, V₁)} {m : Fin n → Γ(F, V₂)} {c : Fin n → Γ(X, V₁ ⊓ V₂)}
    (e : resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) s = ∑ i, c i • resM F (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (m i))
    (h₁ : ⊤ ≤ x ⁻¹ᵁ V₁) (h₂ : ⊤ ≤ x ⁻¹ᵁ V₂) (h : ⊤ ≤ x ⁻¹ᵁ (V₁ ⊓ V₂)) :
    tanEv t hv h₁ (θ.app V₁ s) = ∑ i, ev x _ h (c i) * tanEv t hv h₂ (θ.app V₂ (m i)) := by
  let L : Γ(GlobalTheory.LieVB.omega t.G, V₁ ⊓ V₂) →+ k := AddMonoidHom.mk' (tanEv t hv h) (tanEv_add t hv h)
  have e₁ : tanEv t hv h₁ (θ.app V₁ s) = L (θ.app _ (resM F (inf_le_left : V₁ ⊓ V₂ ≤ V₁) s)) := by
    rw [app_resM]
    exact (tanEv_resM t hv h inf_le_left _).symm
  rw [e₁, e, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, app_resM]
  refine (tanEv_smul t hv h _ _).trans ?_
  rw [tanEv_resM t hv h inf_le_right]
  rfl

theorem annih : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z₁.X) (α : D.C.A), ⊤ ≤ (z ≫ g₀) ⁻¹ᵁ D.C.B α → ∃ (n' : ℕ) (a : Matrix (Fin n') (Fin (D.C.n α)) R) (a' : Matrix (Fin (D.C.n α)) (Fin n') R), a * a' = 1 ∧ a' * a = 1 ∧ ∀ (τ : (Y Z₁.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z₁.i).t (Y Z.i).t τ) (u : Vecs Dw (Y Z₁.i).t K), LocM.IsTrans Z.i Z₁.i τ mu → Z₁.FlagAt (spMap (algebraMap R K) ≫ z) u → ∀ (y : Sp K ⟶ Z.X), y = spMap (algebraMap R K) ≫ z ≫ g₀ → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ D.C.B α) (v : TanM (y ≫ Z.π) (Y Z.i).t.G) (i : Fin (Dw.mult t.σ)), (i : ℕ) < t.k → (tv v).left = u t.σ i ≫ mu.φ → ∀ j : Fin n', t.k ≤ (j : ℕ) → ∑ l, algebraMap R K (a j l) * D.crd α K y hy v l = 0 := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW t Z g D hg hL Z₁ g₀ hg₀ ⟨_, g₁, hg₁, hH⟩ R K _ _ _ _ z α hα
  obtain rfl : g₁ = g₀ ≫ g := MapUniq.isMap_unique E H Dw Xo p W Y i₀ hp hW _ _ _ _ hg₁ (MapComp.isMap_comp hg₀ hg)
  obtain ⟨U, hU, V₁, n', m₁, a₁, hx, hUV, hm₁, hA⟩ := hH (z (IsLocalRing.closedPoint R))
  have hzU : ⊤ ≤ z ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of R) z hx).ge
  obtain ⟨V, m, hV, hm, hc⟩ := hL α
  obtain ⟨T, T', hT, hT', hTm⟩ := exists_trans hm₁ hm
  have hz₁ : ⊤ ≤ (z ≫ g₀ ≫ g) ⁻¹ᵁ V₁ := FlagMod.le_preimage_map _ hUV hzU
  have hz₂ : ⊤ ≤ (z ≫ g₀ ≫ g) ⁻¹ᵁ V := by
    rw [← Category.assoc]
    exact FlagMod.le_preimage_map _ hV hα
  have hz := FlagMod.le_preimage_inf hz₁ hz₂
  refine ⟨n', a₁.1.map (ev z U hzU) * T.map (ev _ _ hz), T'.map (ev _ _ hz) * (a₁⁻¹).1.map (ev z U hzU), ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (T.map _), ← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((a₁⁻¹).1.map _), ← Matrix.map_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, ← Matrix.map_mul, hT',
      Matrix.map_one _ (map_zero _) (map_one _)]
  intro τ mu u hτ hu y ey hy v i hi hv j hj
  have hyo : Set.range y ⊆ Z.opn := by
    rintro _ ⟨q, rfl⟩
    rw [ey, ← Category.assoc, Scheme.Hom.comp_apply]
    exact CommonMod.map_mem_opn hg₀ (MapComp.range_subset_opn Z₁ hu ⟨q, rfl⟩)
  obtain ⟨τ₀, mu₀, -, hτ₀, e₀, -⟩ := hg.2 K y hyo
  have e₀' : (y ≫ Z.π) ≫ τ₀ = (y ≫ g) ≫ t.B.π := (Category.assoc _ _ _).trans e₀.symm
  obtain ⟨v', ev'⟩ := (pushE t.B.tMap (y ≫ g) rfl).surjective (pushE mu₀ _ e₀' v)
  have hv' : (tv v').left ≫ t.B.tMap.φ = (tv v).left ≫ mu₀.φ := congrArg (fun q => (tv q).left) ev'
  obtain ⟨mu', hmu'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mu₀ mu
  have ew : spMap ((algebraMap R K).comp (ev z U hzU)) ≫ hU.fromSpec = spMap (algebraMap R K) ≫ z := by
    rw [← MapComp.sp_comp, Category.assoc, FlagMod.spMap_ev]
  have eyg : y ≫ g = spMap (algebraMap R K) ≫ z ≫ g₀ ≫ g := by simp only [ey, Category.assoc]
  have hyV : ⊤ ≤ (y ≫ g) ⁻¹ᵁ (V₁ ⊓ V) := eyg ▸ FlagMod.le_preimage_comp _ hz
  have hy₁ : ⊤ ≤ (y ≫ g) ⁻¹ᵁ V₁ := FlagMod.le_preimage_mono inf_le_left hyV
  have hy₂ : ⊤ ≤ (y ≫ g) ⁻¹ᵁ V := FlagMod.le_preimage_mono inf_le_right hyV
  have key := hA K ((algebraMap R K).comp (ev z U hzU)) (tv v').left
  rw [ew, Category.assoc, ← eyg] at key
  replace key := key (isTan_tv v') hy₁ ⟨τ ≫ τ₀, mu', u, i,
    MapComp.isTrans_comp hg.1.1 hg₀.1.1 hτ₀ hτ mu' hmu', hu, hi, by rw [hv', hv, hmu', Category.assoc]⟩ j hj
  have eev : ev (y ≫ g) _ hyV = (algebraMap R K).comp (ev _ _ hz) :=
    (FlagMod.ev_congr eyg _ _ (FlagMod.le_preimage_comp _ hz)).trans (FlagMod.ev_spMap _ _ _ _ _)
  rw [← key]
  simp only [hc τ₀ mu₀ hτ₀ K y hy hyo v _ (isTan_tv v') hy₂ hv', Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul,
    Matrix.map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [tanEv_trans t.B.t (isTan_tv v') t.L.N.incl (hTm l) hy₁ hy₂ hyV, eev, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

end GlobalTheory.GrCl.Annih
