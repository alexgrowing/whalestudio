import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratingSectionsProjectiveMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationUniqueQuotient
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.LineQuot
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover)

namespace GlobalTheory.PluckerMap

attribute [local instance] Abelian.hasFiniteBiproducts

theorem sum_prod_mul_det {R N ι : Type} [CommRing R] [AddCommGroup N] [Module R N] [Fintype ι] {d : ℕ}
    (b : Module.Basis (Fin d) R N) (v : ι → N) (c : Fin d → ι → R) (h : ∀ a, b a = ∑ m, c a m • v m) :
    ∑ I : Fin d → ι, (∏ a, c a (I a)) * b.det (fun a => v (I a)) = 1 := by
  classical
  rw [← b.det_self, show (⇑b : Fin d → N) = fun a => ∑ m, c a m • v m from funext h]
  refine Eq.trans ?_ (b.det.toMultilinearMap.map_sum fun a m => c a m • v m).symm
  exact Finset.sum_congr rfl fun I _ => (b.det.toMultilinearMap.map_smul_univ _ _).symm

theorem det_update_eq_repr {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {d : ℕ}
    (b : Module.Basis (Fin d) R N) (a : Fin d) (w : N) : b.det (Function.update b a w) = b.repr w a := by
  conv_lhs => rw [← b.sum_repr w]
  rw [AlternatingMap.map_update_sum, Finset.sum_eq_single a]
  · rw [AlternatingMap.map_update_smul, Function.update_eq_self, b.det_self, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [AlternatingMap.map_update_smul, b.det.map_update_self _ hj.symm, smul_zero]
  · simp

variable {T : Scheme.{0}} {L Q F : T.Modules} {d : ℕ}

theorem eq_repr_smul {U V : T.Opens} {e : Fin 1 → Γ(L, U)} (he : IsFrame e) (h : V ≤ U) (s : Γ(L, V)) :
    s = (he.basis h).repr s 0 • resM L h (e 0) := by
  conv_lhs => rw [← (he.basis h).sum_repr s]
  rw [Fin.sum_univ_one, IsFrame.basis_apply]

theorem isFrame_basicOpen {U V : T.Opens} {e : Fin d → Γ(F, U)} (he : IsFrame e) (h : V ≤ U)
    (s : Fin d → Γ(F, V)) :
    IsFrame fun a => resM F (T.basicOpen_le ((he.basis h).det s)) (s a) :=
  isFrame_iff.2 fun W hW => by
    have hu := ExMap.isUnit_resG_basicOpen _ hW
    rw [he.resG_det, ← Module.Basis.is_basis_iff_det] at hu
    simp only [resM_resM]
    exact ⟨hu.1, hu.2.ge⟩

theorem exists_frame {M : ℕ} {u : Fin (M + 1) → (L ⟶ Q)} (hL : IsVB L 1) (hQ : IsVB Q d) (hu : JointEpi u) (x : T) :
    ∃ (I : Fin d → Fin (M + 1)) (W : T.Opens) (t : Γ(L, W)), x ∈ W ∧ (IsFrame fun _ : Fin 1 => t) ∧
      IsFrame fun a => (u (I a)).app W t := by
  have hp : Epi (biproduct.desc u) := Preadditive.epi_of_cancel_zero _ fun {Z} a ha =>
    hu Z a fun j => by simpa using congrArg (biproduct.ι (fun _ : Fin (M + 1) => L) j ≫ ·) ha
  obtain ⟨U₁, e', hx₁, he'⟩ := hL x
  obtain ⟨U₂, e, -, hx₂, h₂, he⟩ := hQ.exists_affine hx₁
  choose O hO hxO t ht using fun a => exists_app_eq_of_epi (biproduct.desc u) (e a) hx₂
  let W : T.Opens := U₂ ⊓ Finset.univ.inf O
  have hxW : x ∈ W := ⟨hx₂, by rw [Opens.coe_finset_inf]; simpa using hxO⟩
  have hW (a : Fin d) : W ≤ O a := inf_le_right.trans (Finset.inf_le (Finset.mem_univ a))
  have hW' : W ≤ U₁ := inf_le_left.trans h₂
  let B := he.basis (inf_le_left : W ≤ U₂)
  have h1 := sum_prod_mul_det B (fun m => (u m).app W (resM L hW' (e' 0)))
    (fun a m => (he'.basis hW').repr ((biproduct.π (fun _ : Fin (M + 1) => L) m).app W (resM _ (hW a) (t a))) 0)
    fun a => by
      rw [IsFrame.basis_apply, ← resM_resM (hO a) (hW a), ← ht, ← app_resM, desc_app]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Scheme.Modules.Hom.app_smul, ← eq_repr_smul he']
  obtain ⟨I, -, hI⟩ := IsLocalRing.exists_of_isUnit_sum (s := Finset.univ)
    (f := fun I : Fin d → Fin (M + 1) => T.presheaf.germ W x hxW (_ * B.det fun a => (u (I a)).app W (resM L hW' (e' 0))))
    (by rw [← map_sum, h1, map_one]; exact isUnit_one)
  rw [map_mul] at hI
  have hf := isFrame_basicOpen he (inf_le_left : W ≤ U₂) fun a => (u (I a)).app W (resM L hW' (e' 0))
  refine ⟨I, _, resM L ((T.basicOpen_le _).trans hW') (e' 0),
    (T.mem_basicOpen _ x hxW).2 (isUnit_of_mul_isUnit_right hI), ?_, ?_⟩
  · have := he'.res ((T.basicOpen_le (B.det fun a => (u (I a)).app W (resM L hW' (e' 0)))).trans hW')
    rwa [show (fun i => resM L _ (e' i)) = fun _ => resM L _ (e' 0) from funext fun i => by rw [Subsingleton.elim i 0]] at this
  · convert hf using 2
    rw [← app_resM, resM_resM]

def frameLocus (v : Fin d → Γ(F, ⊤)) : T.Opens :=
  ⨆ W : {W : T.Opens // IsFrame fun a => resM F (le_top : W ≤ ⊤) (v a)}, W.1

theorem le_frameLocus {v : Fin d → Γ(F, ⊤)} {W : T.Opens} (h : IsFrame fun a => resM F (le_top : W ≤ ⊤) (v a)) :
    W ≤ frameLocus v := le_iSup (fun W : {W : T.Opens // IsFrame fun a => resM F (le_top : W ≤ ⊤) (v a)} => W.1) ⟨W, h⟩

theorem isFrame_frameLocus (v : Fin d → Γ(F, ⊤)) : IsFrame fun a => resM F (le_top : frameLocus v ≤ ⊤) (v a) :=
  isFrame_of_forall_exists fun V h x hx => by
    obtain ⟨W, hW⟩ := Opens.mem_iSup.1 (h hx)
    refine ⟨V ⊓ W.1, inf_le_left, ⟨hx, hW⟩, ?_⟩
    simpa only [resM_resM] using W.2 _ inf_le_right

theorem isCoordFamily {N : ℕ} (v : Fin (N + 1) → Fin d → Γ(F, ⊤))
    (hv : ∀ x : T, ∃ (i : Fin (N + 1)) (W : T.Opens), x ∈ W ∧ IsFrame fun a => resM F (le_top : W ≤ ⊤) (v i a)) :
    ProjSpace.IsCoordFamily (fun i => frameLocus (v i))
      fun i j => ((isFrame_frameLocus (v i)).basis le_rfl).det fun a => resM F le_top (v j a) where
  cover := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, W, hx, hW⟩ := hv x
    exact Opens.mem_iSup.2 ⟨i, le_frameLocus hW hx⟩
  self i := by
    have := ((isFrame_frameLocus (v i)).basis le_rfl).det_self
    rwa [IsFrame.coe_basis, funext fun a => resM_resM _ _ (v i a)] at this
  mul i j k := by
    simp only [IsFrame.resG_det, resM_resM]
    rw [(isFrame_frameLocus (v i)).det_eq_detUnit_mul (isFrame_frameLocus (v j)) inf_le_left inf_le_right
      (fun a => resM F le_top (v k a)), IsFrame.val_detUnit]
    simp only [resM_resM]
  basicOpen_le i j := le_frameLocus (by
    simpa only [resM_resM] using isFrame_basicOpen (isFrame_frameLocus (v i)) le_rfl fun a => resM F le_top (v j a))

section Rel

variable {k : Type} [CommRing k] {N M : ℕ}

def PRel (φ : T ⟶ PSpace k N) (σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1))) (u : Fin (M + 1) → (L ⟶ Q)) : Prop :=
  ∀ (i : Fin (N + 1)) (x : T), x ∈ φ ⁻¹ᵁ ProjSpace.chart k N i →
    ∃ (W : T.Opens) (h : W ≤ φ ⁻¹ᵁ ProjSpace.chart k N i) (t : Γ(L, W)), x ∈ W ∧ (IsFrame fun _ : Fin 1 => t) ∧
      (IsFrame fun a => (u (σ i a)).app W t) ∧ ∀ m, (u m).app W t =
        ∑ a, ProjSpace.pullRatio φ W i h (σ.symm (Function.update (σ i) a m)) • (u (σ i a)).app W t

theorem exists_prel (f : T ⟶ Sp k) (σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1))) {u : Fin (M + 1) → (L ⟶ Q)}
    (hL : IsVB L 1) (hQ : IsVB Q d) (hu : JointEpi u) :
    ∃ φ : T ⟶ PSpace k N, φ ≫ PSpace.str k N = f ∧ PRel φ σ u := by
  let v (m : Fin (M + 1)) : Γ(homMod L Q, ⊤) := (homGlobalEquiv L Q).symm (u m)
  let ε {W : T.Opens} {t : Γ(L, W)} (ht : IsFrame fun _ : Fin 1 => t) (V : T.Opens) (h : V ≤ W) :
      Γ(homMod L Q, V) ≃ₗ[Γ(T, V)] Γ(Q, V) := PtNorm.homPi ht h ≪≫ₗ LinearEquiv.funUnique (Fin 1) _ _
  have hε {W : T.Opens} {t : Γ(L, W)} (ht : IsFrame fun _ : Fin 1 => t) (V : T.Opens) (h : V ≤ W) (m : Fin (M + 1)) :
      ε ht V h (resM _ le_top (v m)) = resM Q h ((u m).app W t) := app_resM (u m) h t
  let H := isCoordFamily (fun i a => v (σ i a)) fun x => by
    obtain ⟨I, W, t, hx, ht, hf⟩ := exists_frame hL hQ hu x
    refine ⟨σ.symm I, W, hx, hf.map_of_linearEquiv (fun V h => (ε ht V h).symm) fun V h a => ?_⟩
    rw [LinearEquiv.symm_apply_eq, resM_resM, hε, Equiv.apply_symm_apply]
  refine ⟨H.toHom f, H.toHom_str f, fun i x hx => ?_⟩
  rw [H.toHom_preimage] at hx
  obtain ⟨W, e, -, hxW, hW, he⟩ := hL.exists_affine hx
  obtain ⟨t, rfl⟩ : ∃ t, e = fun _ => t := ⟨e 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  have hv := isFrame_frameLocus fun a => v (σ i a)
  refine ⟨W, hW.trans (H.le_toHom_preimage f i), t, hxW, he,
    (hv.res hW).map_of_linearEquiv (ε he) fun V h a => by rw [resM_resM, resM_resM, hε], fun m => ?_⟩
  have h1 := congrArg (ε he W le_rfl) ((hv.basis hW).sum_repr (resM _ le_top (v m)))
  rw [hε, resM_self, map_sum] at h1
  refine h1.symm.trans (Finset.sum_congr rfl fun a _ => ?_)
  rw [map_smul, IsFrame.basis_apply, resM_resM, hε, resM_self,
    ← ProjSpace.resG_pullRatio (hi := H.le_toHom_preimage f i) hW, H.pullRatio_toHom f, IsFrame.resG_det,
    ← det_update_eq_repr]
  congr 2
  funext b
  simp only [resM_resM, Equiv.apply_symm_apply, IsFrame.coe_basis]
  exact (Function.apply_update (fun _ m => resM (homMod L Q) (le_top : W ≤ ⊤) (v m)) (σ i) a m b).symm

variable {φ : T ⟶ PSpace k N} {σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1))} {u : Fin (M + 1) → (L ⟶ Q)}

theorem PRel.pullback [L.IsQuasicoherent] [Q.IsQuasicoherent] (h : PRel φ σ u) {S : Scheme.{0}} (g : S ⟶ T) :
    PRel (g ≫ φ) σ fun m => (Scheme.Modules.pullback g).map (u m) := by
  intro i y hy
  obtain ⟨W, hW, t, hx, ht, hf, hr⟩ := h i (g y) hy
  refine ⟨g ⁻¹ᵁ W, g.preimage_mono hW, QCoh.pullbackSections g L le_rfl t, hx, ht.pullback g, ?_, fun m => ?_⟩
  · simpa only [QCoh.pullback_map_app_pullbackSections] using hf.pullback g
  · simp only [QCoh.pullback_map_app_pullbackSections]
    rw [hr m, map_sum]
    simp only [QCoh.pullbackSections_smul]
    exact Finset.sum_congr rfl fun a _ => by rw [← ProjSpace.appLE_pullRatio]

theorem PRel.pre (h : PRel φ σ u) {L' : T.Modules} (α : L ≅ L') : PRel φ σ fun m => α.inv ≫ u m := by
  intro i x hx
  obtain ⟨W, hW, t, hx, ht, hf, hr⟩ := h i x hx
  have e (m) : (α.inv ≫ u m).app W (α.hom.app W t) = (u m).app W t := by
    rw [QCoh.app_app, α.hom_inv_id_assoc]
  exact ⟨W, hW, α.hom.app W t, hx, ht.map_iso α.hom, by simpa only [e] using hf, by simpa only [e] using hr⟩

theorem PRel.exists_desc_app (h : PRel φ σ u) (i : Fin (N + 1)) (x : T) (hx : x ∈ φ ⁻¹ᵁ ProjSpace.chart k N i) :
    ∃ (W : T.Opens) (hW : W ≤ φ ⁻¹ᵁ ProjSpace.chart k N i), x ∈ W ∧ ∀ (V : T.Opens) (hV : V ≤ W),
      (∀ s : Fin d → Γ(L, V), ∑ a, (u (σ i a)).app V (s a) = 0 → ∀ a, s a = 0) ∧
      ∀ s : Fin (M + 1) → Γ(L, V), ∑ m, (u m).app V (s m) = ∑ a, (u (σ i a)).app V
        (∑ m, ProjSpace.pullRatio φ V i (hV.trans hW) (σ.symm (Function.update (σ i) a m)) • s m) := by
  obtain ⟨W, hW, t, hx, ht, hf, hr⟩ := h i x hx
  refine ⟨W, hW, hx, fun V hV => ⟨fun s hs a => ?_, fun s => ?_⟩⟩
  · have := (hf V hV).1 (a₁ := fun a => (ht.basis hV).repr (s a) 0) (a₂ := 0) (by
      rw [map_zero, ← hs, Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← app_resM, ← Scheme.Modules.Hom.app_smul, ← eq_repr_smul ht])
    rw [eq_repr_smul ht hV (s a), congrFun this a, Pi.zero_apply, zero_smul]
  · simp only [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [eq_repr_smul ht hV (s m), Scheme.Modules.Hom.app_smul, app_resM, hr m, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, app_resM, resM_smul, ProjSpace.resG_pullRatio,
      smul_comm]

theorem PRel.exists_factor {Q' : T.Modules} {u' : Fin (M + 1) → (L ⟶ Q')} (h : PRel φ σ u) (h' : PRel φ σ u')
    (hu : JointEpi u) : ∃ e : Q ⟶ Q', ∀ m, u m ≫ e = u' m := by
  have hepi : Epi (biproduct.desc u) := Preadditive.epi_of_cancel_zero _ fun {Z} a ha =>
    hu Z a fun j => by simpa using congrArg (biproduct.ι (fun _ : Fin (M + 1) => L) j ≫ ·) ha
  choose i hi using fun x : T => ProjSpace.exists_mem_chart k N (φ x)
  choose W hW hx H using fun x => h.exists_desc_app (i x) x (hi x)
  choose W' hW' hx' H' using fun x => h'.exists_desc_app (i x) x (hi x)
  have loc : ∀ (V : T.Opens) (t : Γ(⨁ fun _ : Fin (M + 1) => L, V)),
      (biproduct.desc u).app V t = 0 → (biproduct.desc u').app V t = 0 := by
    intro V t h0
    refine sec_ext_of_cover (fun x => V ⊓ W x ⊓ W' x) (fun _ => inf_le_left.trans inf_le_left)
      (fun y hy => Opens.mem_iSup.2 ⟨y, ⟨⟨hy, hx y⟩, hx' y⟩⟩) fun x => ?_
    have h1 := congrArg (resM Q (inf_le_left.trans inf_le_left : V ⊓ W x ⊓ W' x ≤ V)) h0
    rw [← app_resM, map_zero, desc_app, (H x _ (inf_le_left.trans inf_le_right)).2] at h1
    rw [← app_resM, map_zero, desc_app, (H' x _ inf_le_right).2]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [(H x _ (inf_le_left.trans inf_le_right)).1 _ h1 a, map_zero]
  have hk : kernel.ι (biproduct.desc u) ≫ biproduct.desc u' = 0 := by
    ext V x
    have h := congrArg (fun f => f.app V x) (kernel.condition (biproduct.desc u))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h ⊢
    exact loc V _ h
  refine ⟨Abelian.epiDesc _ _ hk, fun j => ?_⟩
  rw [← biproduct.ι_desc u j, Category.assoc, Abelian.comp_epiDesc, biproduct.ι_desc]

end Rel

theorem hom_ext_map_biproduct {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (Φ : C ⥤ D)
    [Φ.Additive] {ι : Type} [Fintype ι] (f : ι → C) [HasBiproduct f] {Z : D} {a b : Φ.obj (⨁ f) ⟶ Z}
    (h : ∀ j, Φ.map (biproduct.ι f j) ≫ a = Φ.map (biproduct.ι f j) ≫ b) : a = b := by
  have e (c : Φ.obj (⨁ f) ⟶ Z) : c = ∑ j, Φ.map (biproduct.π f j) ≫ Φ.map (biproduct.ι f j) ≫ c := by
    simp only [← Functor.map_comp_assoc, ← Preadditive.sum_comp, ← Functor.map_sum, biproduct.total, Φ.map_id,
      Category.id_comp]
  rw [e a, e b]
  simp only [h]

theorem exists_epi_biproduct {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {E : B.Modules} {r : ℕ} (hE : IsVB E r) :
    ∃ (M : ℕ) (L : B.Modules) (a : (⨁ fun _ : Fin (M + 1) => L) ⟶ E), IsVB L 1 ∧ Epi a := by
  have := hE.isFiniteQC
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hq
  obtain ⟨n, N, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := isVB_toMod (Twist.isLB_lbZPow hA.isLB (-n))
  generalize LB.toMod (lbZPow A (-n)) = L at φ hφ hL
  refine ⟨N, L, biproduct.desc (Fin.cons 0 fun j => Sigma.ι (fun _ => L) j ≫ φ), hL,
    (Preadditive.epi_iff_cancel_zero _).2 fun Z b hb => ?_⟩
  rw [← cancel_epi φ]
  refine Sigma.hom_ext _ _ fun j => ?_
  simpa using biproduct.ι _ j.succ ≫= hb

theorem exists_toPSpace_of_isSubbundle : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k), IsProjOver q → ∀ (E : B.Modules) (n m : ℕ), IsVB E n → m ≤ n → ∀ (G : Scheme.{0}) (γ : G ⟶ B) (P : G.Modules) (j : P ⟶ (Scheme.Modules.pullback γ).obj E), IsVB P m → IsSubbundle j → ∃ (N : ℕ) (φ : G ⟶ PSpace k N), φ ≫ PSpace.str k N = γ ≫ q ∧ ∀ (T : Scheme.{0}) (g₁ g₂ : T ⟶ G) (g : T ⟶ B) (w₁ : g₁ ≫ γ = g) (w₂ : g₂ ≫ γ = g), g₁ ≫ φ = g₂ ≫ φ → ∃ e : (Scheme.Modules.pullback g₁).obj P ≅ (Scheme.Modules.pullback g₂).obj P, e.hom ≫ (Scheme.Modules.pullback g₂).map j ≫ (Scheme.Modules.pullbackComp g₂ γ).hom.app E ≫ (Scheme.Modules.pullbackCongr w₂).hom.app E = (Scheme.Modules.pullback g₁).map j ≫ (Scheme.Modules.pullbackComp g₁ γ).hom.app E ≫ (Scheme.Modules.pullbackCongr w₁).hom.app E := by
  intro k _ B q hq E n m hE _ G γ P j hP hj
  obtain ⟨M, L, a, hL, ha⟩ := exists_epi_biproduct hq hE
  obtain ⟨d, hQ⟩ := hj.isVB_cokernel
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := Fin d → Fin (M + 1)))
  let σ : Fin (N + 1) ≃ (Fin d → Fin (M + 1)) := (Fintype.equivFinOfCardEq hN).symm
  let b (i : Fin (M + 1)) : L ⟶ E := biproduct.ι (fun _ : Fin (M + 1) => L) i ≫ a
  have hext {T : Scheme.{0}} (g : T ⟶ B) {Z : T.Modules} {x y : (Scheme.Modules.pullback g).obj E ⟶ Z}
      (h : ∀ i, (Scheme.Modules.pullback g).map (b i) ≫ x = (Scheme.Modules.pullback g).map (b i) ≫ y) : x = y := by
    rw [← cancel_epi ((Scheme.Modules.pullback g).map a)]
    exact hom_ext_map_biproduct _ _ fun i => by simpa [b] using h i
  let u (i : Fin (M + 1)) := (Scheme.Modules.pullback γ).map (b i) ≫ cokernel.π j
  obtain ⟨φ, hφ, hr⟩ := exists_prel (γ ≫ q) σ (u := u) (hL.pullback γ) hQ fun Z c hc => by
    rw [← cancel_epi (cokernel.π j)]
    exact hext γ fun i => by simpa [u] using hc i
  have := (hL.pullback γ).isQuasicoherent
  have := hQ.isQuasicoherent
  have := hj.mono
  have key (T : Scheme.{0}) (g₁ g₂ : T ⟶ G) (g : T ⟶ B) (w₁ : g₁ ≫ γ = g) (w₂ : g₂ ≫ γ = g) (h : g₁ ≫ φ = g₂ ≫ φ) :
      ∃ e : (Scheme.Modules.pullback g₁).obj P ⟶ (Scheme.Modules.pullback g₂).obj P,
        e ≫ (Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E =
          (Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E := by
    have hu (g' : T ⟶ G) (w : g' ≫ γ = g) (i : Fin (M + 1)) :
        ((cmp g' γ w).app L).inv ≫ (Scheme.Modules.pullback g').map (u i) = (Scheme.Modules.pullback g).map (b i) ≫
          (cmp g' γ w).inv.app E ≫ (Scheme.Modules.pullback g').map (cokernel.π j) := by
      rw [Iso.inv_comp_eq, Iso.app_hom, ← cmp_naturality_assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp]
    have h₁ := (hr.pullback g₁).pre ((cmp g₁ γ w₁).app L)
    have h₂ := (hr.pullback g₂).pre ((cmp g₂ γ w₂).app L)
    rw [h] at h₁
    simp only [hu] at h₁ h₂
    obtain ⟨e, he⟩ := h₁.exists_factor h₂ fun Z c hc => by
      rw [← cancel_epi ((Scheme.Modules.pullback g₁).map (cokernel.π j)), ← cancel_epi ((cmp g₁ γ w₁).inv.app E)]
      exact hext g fun i => by simpa using hc i
    have he' : (cmp g₁ γ w₁).inv.app E ≫ (Scheme.Modules.pullback g₁).map (cokernel.π j) ≫ e =
        (cmp g₂ γ w₂).inv.app E ≫ (Scheme.Modules.pullback g₂).map (cokernel.π j) :=
      hext g fun i => by simpa using he i
    have hex := (ShortComplex.exact_cokernel j).map_of_epi_of_preservesCokernel (Scheme.Modules.pullback g₂)
      (inferInstanceAs (Epi (cokernel.π j))) inferInstance
    have : Mono ((ShortComplex.mk j (cokernel.π j) (cokernel.condition j)).map (Scheme.Modules.pullback g₂)).f :=
      (SubPull.isSubbundle_pullback _ _ g₂ _ _ _ m hP hj).mono
    obtain ⟨c, hc⟩ : ∃ c, c ≫ (Scheme.Modules.pullback g₂).map j =
        (Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E ≫ (cmp g₂ γ w₂).inv.app E := hex.lift' _ (by
      change _ ≫ (Scheme.Modules.pullback g₂).map (cokernel.π j) = 0
      rw [Category.assoc, Category.assoc, ← he', Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
        cokernel.condition]
      simp)
    exact ⟨c, by rw [reassoc_of% hc]; simp⟩
  refine ⟨N, φ, hφ, fun T g₁ g₂ g w₁ w₂ h => ?_⟩
  obtain ⟨e, he⟩ := key T g₁ g₂ g w₁ w₂ h
  obtain ⟨e', he'⟩ := key T g₂ g₁ g w₂ w₁ h.symm
  have := (SubPull.isSubbundle_pullback _ _ g₁ _ _ _ m hP hj).mono
  have := (SubPull.isSubbundle_pullback _ _ g₂ _ _ _ m hP hj).mono
  exact ⟨⟨e, e', by
      rw [← cancel_mono ((Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E), Category.assoc, he', he,
        Category.id_comp], by
      rw [← cancel_mono ((Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E), Category.assoc, he, he',
        Category.id_comp]⟩, he⟩

end GlobalTheory.PluckerMap

end
