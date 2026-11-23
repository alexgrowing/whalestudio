import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SplitMapEqZeroOfMemAnn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.GroupBplus
open GlobalTheory.DeRham (spOver)
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChainPts.SysB.OmegaRes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {A A' : Type} [CommRing A] [CommRing A']

open GlobalTheory.LieVB GlobalTheory.VB GlobalTheory.HTSheaf GlobalTheory.LocM GlobalTheory.LocM.TanPair in

theorem exists_dual_family (t : SAB H (Sp A)) {G' : Over (Sp A')} [GrpObj G'] (σ : A →+* A') {ψ : G'.left ⟶ t.G.left}
    (hψ : IsGrpPullback G' t.G (spMap σ) ψ) [QuasiSeparated G'.hom] :
    ∃ (m : ℕ) (v : Fin m → Pdiv.LieG t.G) (v' : Fin m → Pdiv.LieG G') (e : Fin m → Pdiv.omega G'),
      (∀ i, (v' i).1.left ≫ ψ = spMap (Formalism.L2.Pj.dualMap σ) ≫ (v i).1.left) ∧ ∀ d : Pdiv.omega G', d = ∑ i, d.1 (v' i) • e i := by
  have := t.semi
  have := t.semi.smooth
  have : Smooth G'.hom := MorphismProperty.of_isPullback hψ.1 ‹_›
  obtain ⟨h1, h2⟩ := GlobalTheory.FramesFGP.finite_projective_top (omega t.G) (exists_isFrame_omega t.G)
  obtain ⟨m, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective Γ(Sp A, ⊤) Γ(omega t.G, ⊤)
  have hv (i : Fin m) : ∃ v : Pdiv.LieG t.G, ∀ s, dualApp (tangent v) le_top s = g s i := by
    obtain ⟨lam, hlam⟩ := (GlobalTheory.OmegaGlobal.dualApp_top_bijective (omega t.G)).2 (LinearMap.proj i ∘ₗ g)
    obtain ⟨v, rfl⟩ := TangentSurj.tangent_surjective A t.G lam
    exact ⟨v, fun s => LinearMap.congr_fun hlam s⟩
  choose v hv using hv
  have hid : IsGrpPullback t.G t.G (𝟙 _) (𝟙 _) := @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl t.G) (inferInstanceAs (IsMonHom (𝟙 t.G)))
  have ht (i : Fin m) : IsTanAtG t (𝟙 _) (v i).1.left := by
    simpa only [Category.comp_id] using isTanAtG_lieG hid (v i)
  have ht' (i : Fin m) : IsTanAtG t (spMap σ) (spMap (Formalism.L2.Pj.dualMap σ) ≫ (v i).1.left) :=
    LieMet.isTan_map σ (Category.comp_id _) (ht i)
  choose v' hv' using fun i => exists_lieG hψ (ht' i)
  have k : (⊤ : (Sp A').Opens) ≤ spMap σ ⁻¹ᵁ ⊤ := le_top
  have k₀ : (⊤ : (Sp A).Opens) ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ := le_top
  have val (i : Fin m) (s : Γ(omega t.G, ⊤)) : (toOmega G' (pb hψ k s)).1 (v' i) =
      σ ((Scheme.ΓSpecIso (.of A)).hom (g (pb hid k₀ s) i)) := by
    refine (tanEv_eq hψ (v' i) (ht' i) (hv' i) k s).symm.trans ?_
    refine (tanEv_baseChange E H _ t A (𝟙 _) ⊤ k₀ _ (ht i) A' σ (ht' i) k s).trans (congrArg σ ?_)
    rw [tanEv_eq hid (v i) (ht i) (Category.comp_id _) k₀ s, hv]
    rfl
  have sm (a : Γ(Sp A, ⊤)) (s : Γ(omega t.G, ⊤)) : toOmega G' (pb hψ k (a • s)) =
      σ ((Scheme.ΓSpecIso (.of A)).hom a) • toOmega G' (pb hψ k s) := by
    rw [pb_smul, ← toOmega_smul]
    congr 2
    refine (appLE_top _ _).trans ?_
    refine .trans ?_ congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ)) ((Scheme.ΓSpecIso (.of A)).hom a)).symm
    exact congrArg _ (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of A)) a).symm
  refine ⟨m, v, v', fun i => toOmega G' (pb hψ k (f (Pi.single i 1))), hv', fun d => ?_⟩
  obtain ⟨s, rfl⟩ := (GlobalTheory.OmegaGlobal.toOmega_bijective A' G'
    ⟨tangent_injective A' G', TangentSurj.tangent_surjective A' G'⟩).2 d
  have hs : s ∈ Submodule.span Γ(Sp A', ⊤) (Set.range (pb hψ k)) := by
    rw [span_range_pb hψ (isAffineOpen_top _) (isAffineOpen_top _)]; trivial
  induction hs using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨s, rfl⟩ := hx
    simp only [val, ← sm, ← map_sum, ← map_smul]
    rw [← pi_eq_sum_univ', show f (g (pb hid k₀ s)) = pb hid k₀ s from LinearMap.congr_fun hfg _,
      pb_pb hid hψ hψ (Category.comp_id _) (Category.comp_id _)]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    refine (congrArg₂ (· + ·) hx hy).trans ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
  | smul a x _ hx =>
    obtain ⟨a, rfl⟩ : ∃ b, a = cst A' b := ⟨_, (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of A')) a).symm⟩
    rw [toOmega_smul]
    refine (congrArg (a • ·) hx).trans ?_
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm

variable (p n : ℕ) [Algebra A A']

variable (A A') in

def modMap : ModPow p A n →+* ModPow p A' n := Ideal.quotientMap _ (algebraMap A A') (by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow, map_natCast]
  exact Ideal.mem_span_singleton_self _)

variable (A A') in

def dualMod : DualNumber (ModPow p A n) →ₐ[A] DualNumber (ModPow p A' n) :=
  { dualMap (modMap A A' p n) with
    commutes' := fun r => by
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl', modMap] }

theorem fst_dualMod (z : DualNumber (ModPow p A n)) : (dualMod A A' p n z).fst = modMap A A' p n z.fst := add_zero _

theorem snd_dualMod (z : DualNumber (ModPow p A n)) : (dualMod A A' p n z).snd = modMap A A' p n z.snd := zero_add _

variable (A A') in

theorem dualMod_square : (spOver (dualMod A A' p n)).left ≫ (spOver (epsTo A (ModPow p A n))).left =
    (spOver (epsTo A' (ModPow p A' n))).left ≫ spMap (dualMap (algebraMap A A')) := by
  refine (Cris.spMap_comp _ _).symm.trans (.trans (congrArg spMap ?_) (Cris.spMap_comp _ _))
  refine RingHom.ext fun y => TrivSqZeroExt.ext ?_ ?_
  · exact (fst_dualMod ..).trans ((congrArg _ (fst_epsTo _ y)).trans
      ((fst_epsTo _ (dualMap (algebraMap A A') y)).trans (congrArg (algebraMap A' _) (add_zero _))).symm)
  · exact (snd_dualMod ..).trans ((congrArg _ (snd_epsTo _ y)).trans
      ((snd_epsTo _ (dualMap (algebraMap A A') y)).trans (congrArg (algebraMap A' _) (zero_add _))).symm)

theorem omegaResSt : OmegaResSt := by
  intro E _ _ _ H p _ X tX A A' _ _ _ x t t' φ φ' hφ hφ' GG GG' θ θ' c c' f hc hc' hθ w w' hw
  have := t'.semi
  obtain ⟨ψ, e₁, e₂⟩ : ∃ ψ : t'.G.left ⟶ t.G.left, ψ ≫ φ = φ' ∧ ψ ≫ t.G.hom = t'.G.hom ≫ spMap (algebraMap A A') :=
    ⟨hφ.1.lift φ' _ (hφ'.1.w.trans (Category.assoc ..).symm), hφ.1.lift_fst .., hφ.1.lift_snd ..⟩
  subst e₁
  obtain ⟨m, v, v', e, hv, he⟩ := exists_dual_family t (algebraMap A A') (hφ.cancel hφ' e₂)
  refine Subtype.ext (funext fun n => ?_)
  obtain ⟨-, -, htan⟩ := hc n
  obtain ⟨hsurj, hker, htan'⟩ := hc' n
  obtain ⟨b, hb⟩ := AugCot.d_surjective (Bialgebra.counitAlgHom A (GG.A n)) ((c w).1 n)
  obtain ⟨u, hu⟩ := hsurj (dUnit A' (f.hom.app n (1 ⊗ₜ b)))
  have key (i : Fin m) : ∃ q : A', (w' - u).1 (v' i) = (p : A') ^ n * q := by
    let z : Tors t.G (p ^ n) (DualNumber (ModPow p A' n)) := ⟨spOver (dualMod A A' p n) ≫ (tanTors p n (v i)).1, by
      rw [← MonObj.comp_pow, (tanTors p n (v i)).2, MonObj.comp_one]⟩
    have h3 : (v' i).1.left ≫ ψ ≫ φ = spMap (dualMap (algebraMap A A')) ≫ (v i).1.left ≫ φ :=
      (Category.assoc ..).symm.trans ((congrArg (· ≫ φ) (hv i)).trans (Category.assoc ..))
    have hz : z.1.left ≫ φ = (tanTors p n (v' i)).1.left ≫ ψ ≫ φ := by
      refine .trans ?_ ((Category.assoc (spOver (epsTo A' (ModPow p A' n))).left (v' i).1.left _).trans
        (congrArg (_ ≫ ·) h3)).symm
      refine .trans ?_ ((congrArg (· ≫ (v i).1.left ≫ φ) (dualMod_square A A' p n)).trans (Category.assoc ..))
      exact (congrArg (· ≫ φ) (Category.assoc ..).symm).trans (Category.assoc ..)
    have h1 := hθ n _ z _ hz b
    have h2 := htan' (v' i) u _ hu.symm
    rw [← h1, θ.nat n _ _ (dualMod A A' p n) (tanTors p n (v i)) z rfl, AlgHom.comp_apply, snd_dualMod,
      htan (v i) w b hb] at h2
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ((congrArg _ (hw (v i) (v' i) h3)).trans h2))
  choose q hq using key
  have h0 := (hker (w' - u)).2 ⟨∑ i, q i • e i, by
    rw [he (w' - u), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hq, mul_smul]⟩
  rw [map_sub, hu, sub_eq_zero] at h0
  refine h0.trans ?_
  rw [omegaMap_val, SemiHom.omega_val, ← hb]
  exact ((congrArg (cotMap (f.hom.app n)) (((GG.toBase A').app n).cot_d b)).trans (cotMap_d (f.hom.app n) _)).symm

end GlobalTheory.ChainPts.SysB.OmegaRes

end
