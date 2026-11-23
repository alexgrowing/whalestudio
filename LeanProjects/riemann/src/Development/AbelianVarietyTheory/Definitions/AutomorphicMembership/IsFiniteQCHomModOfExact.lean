import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HomAppHomOfRestrictImage

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.BoundaryLocalData GlobalTheory.ShFam
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC structureModule)
open GlobalTheory.VB GlobalTheory.PtNorm

namespace GlobalTheory.PtNorm

variable {X : Scheme.{0}} {F G : X.Modules} {U : X.Opens} {p : ℕ} {C : SCF p} (z : Sp (intO C.S) ⟶ X) (hp : p ≠ 0)

theorem isGreatest_vals_frame {h : ⊤ ≤ z ⁻¹ᵁ U} {u : Γ(F, U)} (hu : IsFrame fun _ : Fin 1 => u)
    (ν : Γ(F, U ⊓ gen X p) →ₛₗ[evq z hp h] C.S) : IsGreatest (vals z hp ν) ‖ν (resM F inf_le_left u)‖ := by
  refine ⟨⟨u, rfl⟩, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hm := (hu.basis le_rfl).sum_repr m
  rw [Fin.sum_univ_one, IsFrame.basis_apply, resM_self] at hm
  simp only
  rw [← hm, resM_smul, ν.map_smulₛₗ, evq_res, smul_eq_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (evz z h _).2

include hp in

theorem sSup_compSec_frames {E : X.Modules} {r : ℕ} (hE : IsVB E r) (π : E ⟶ F) [Epi π] [IsFiniteQC F] [IsFiniteQC G]
    (hG : IsVB (G.restrict (gen X p).ι) 1) (φ : F.restrict (gen X p).ι ≅ G.restrict (gen X p).ι) (h : ⊤ ≤ z ⁻¹ᵁ U)
    {u : Γ(F, U)} {v : Γ(G, U)} (hu : IsFrame fun _ : Fin 1 => u) (hv : IsFrame fun _ : Fin 1 => v)
    (a : Γ(X, U ⊓ gen X p))
    (ha : homApp (homOfRestrict φ.hom) inf_le_right (resM F inf_le_left u) = a • resM G inf_le_left v) :
    sSup (nrmSet z (homMod E G) (compSec π φ.hom)) = ‖evq z hp h a‖ := by
  have := isLocalRing_intO C.S
  obtain ⟨T, e, hT, hx, hle, he⟩ := hE.exists_affine ((top_le_preimage_iff z).1 h)
  have h' := (top_le_preimage_iff z).2 hx
  obtain ⟨μ, hμ⟩ := exists_isLineForm_gen z hp (h := h') hG hT
  have hc₂ := isGreatest_vals_frame z hp (hv.res hle) μ
  have hc₁ := isGreatest_vals_frame z hp (hu.res hle) (μ.comp (equivOfRestrict φ inf_le_right).toLinearMap)
  have h₃ : T ⊓ gen X p ≤ U ⊓ gen X p := inf_le_inf_right _ hle
  have e₁ := congrArg (resM G h₃) ha
  rw [← homApp_resM, resM_smul, resM_resM, resM_resM] at e₁
  rw [(isGreatest_nrmSet_compSec z hp hE π hT he φ hμ hc₁ hc₂).csSup_eq,
    div_eq_iff (pos_of_isGreatest z hp hT hμ hc₂).ne', resM_resM, resM_resM]
  refine (congrArg (fun t => ‖μ t‖) e₁).trans ?_
  rw [μ.map_smulₛₗ, smul_eq_mul, norm_mul, evz_res (zq z) _ (zq_le z hp h)]

section Coherent

variable {X : Scheme.{0}} {P Q F G : X.Modules}

theorem sec_ext_affine {W : X.Opens} {a b : Γ(G, W)}
    (e : ∀ (T : X.Opens) (h : T ≤ W), IsAffineOpen T → resM G h a = resM G h b) : a = b :=
  GlobalTheory.Twist.sec_ext_of_cover (fun T : {T : X.Opens // IsAffineOpen T ∧ T ≤ W} => T.1) (fun T => T.2.2)
    (fun x hx => by
      obtain ⟨T, hT, hxT, hle⟩ := QCoh.exists_affine_mem_le (U := W) x hx
      exact Opens.mem_iSup.2 ⟨⟨T, hT, hle⟩, hxT⟩) fun T => e T.1 T.2.2 T.2.1

theorem exists_hom_of_exact (φ : Q ⟶ P) (π : P ⟶ F)
    (hex : ∀ T : X.Opens, IsAffineOpen T → Function.Exact (φ.app T) (π.app T))
    (hs : ∀ T : X.Opens, IsAffineOpen T → Function.Surjective (π.app T)) {U : X.Opens}
    (ψ : Γ(homMod P G, U)) (hψ : ∀ (W : X.Opens) (h : W ≤ U) (m : Γ(Q, W)), homApp ψ h (φ.app W m) = 0) :
    ∃ χ : Γ(homMod F G, U), (homMap π (𝟙 G)).app U χ = ψ := by
  have wd (T : X.Opens) (hT : IsAffineOpen T) (h : T ≤ U) (m m' : Γ(P, T))
      (e : π.app T m = π.app T m') : homApp ψ h m = homApp ψ h m' := by
    obtain ⟨q, hq⟩ := (hex T hT (m - m')).1 (by rw [map_sub, e, sub_self])
    rw [← sub_eq_zero, ← map_sub, ← hq, hψ]
  have H (W : X.Opens) (h : W ≤ U) (s : Γ(F, W)) : ∃ t : Γ(G, W), ∀ (T : X.Opens) (h' : T ≤ W),
      IsAffineOpen T → ∀ m : Γ(P, T), π.app T m = resM _ h' s → resM G h' t = homApp ψ (h'.trans h) m := by
    choose m hm using fun T : {T : X.Opens // IsAffineOpen T ∧ T ≤ W} =>
      hs T.1 T.2.1 (resM _ T.2.2 s)
    obtain ⟨t, ht⟩ := GlobalTheory.Twist.exists_sec_of_cover (fun T : {T : X.Opens // IsAffineOpen T ∧ T ≤ W} => T.1)
      (fun T => T.2.2) (fun x hx => by
        obtain ⟨T, hT, hxT, hle⟩ := QCoh.exists_affine_mem_le (U := W) x hx
        exact Opens.mem_iSup.2 ⟨⟨T, hT, hle⟩, hxT⟩) (fun T => homApp ψ (T.2.2.trans h) (m T)) fun T T' =>
      sec_ext_affine fun V hV hA => by
        rw [resM_resM, resM_resM, ← homApp_resM, ← homApp_resM]
        exact wd V hA _ _ _ (by rw [app_resM, app_resM, hm, hm, resM_resM, resM_resM])
    exact ⟨t, fun T h' hT n hn => (ht ⟨T, hT, h'⟩).trans (wd T hT _ _ _ ((hm ⟨T, hT, h'⟩).trans hn.symm))⟩
  choose t ht using H
  refine ⟨homMk (fun W h =>
    { toFun := t W h
      map_add' a b := sec_ext_affine fun T h' hT => ?_
      map_smul' a b := sec_ext_affine fun T h' hT => ?_ }) fun W W' h h' s => sec_ext_affine fun T h'' hT => ?_,
    VB.hom_ext fun W h m => sec_ext_affine fun T h' hT => ?_⟩
  · obtain ⟨m, hm⟩ := hs T hT (resM _ h' a)
    obtain ⟨n, hn⟩ := hs T hT (resM _ h' b)
    rw [map_add, ht W h a T h' hT m hm, ht W h b T h' hT n hn,
      ht W h _ T h' hT (m + n) (by rw [map_add, map_add, hm, hn]), map_add]
  · obtain ⟨n, hn⟩ := hs T hT (resM _ h' b)
    rw [RingHom.id_apply, resM_smul, ht W h b T h' hT n hn,
      ht W h _ T h' hT (_ • n) (by rw [resM_smul, ← hn, Scheme.Modules.Hom.app_smul]), map_smul]
  · obtain ⟨n, hn⟩ := hs T hT (resM _ (h''.trans h') s)
    change resM G h'' (t W' _ _) = resM G h'' (resM G h' (t W h s))
    rw [resM_resM, ht W h s T _ hT n hn, ht W' _ _ T h'' hT n (by rw [hn, resM_resM])]
  · exact (ht W h _ T h' hT (resM P h' m) (app_resM _ _ _)).trans (homApp_resM ψ h h' m)

theorem isFiniteQC_homMod_of_exact [IsLocallyNoetherian X] {r r' : ℕ} (hQ : IsVB Q r') (hP : IsVB P r) (φ : Q ⟶ P)
    (π : P ⟶ F) (hex : ∀ T : X.Opens, IsAffineOpen T → Function.Exact (φ.app T) (π.app T))
    (hs : ∀ T : X.Opens, IsAffineOpen T → Function.Surjective (π.app T)) (w : φ ≫ π = 0) [IsFiniteQC G] :
    IsFiniteQC (homMod F G) := by
  have h₁ : IsFiniteQC (homMod P G) := isFiniteQC_homMod hP
  have h₂ : IsFiniteQC (homMod Q G) := isFiniteQC_homMod hQ
  have h₃ := h₁.isQuasicoherent
  have h₄ := h₂.isQuasicoherent
  have hι (U : X.Opens) : Function.Injective ((homMap π (𝟙 G)).app U) := fun χ χ' e =>
    VB.hom_ext fun W h s => sec_ext_affine fun T h' hT => by
      obtain ⟨m, hm⟩ := hs T hT (resM _ h' s)
      have e' := congrArg (fun ψ : Γ(homMod P G, U) => homApp ψ (h'.trans h) m) e
      rw [← homApp_resM, ← homApp_resM, ← hm]
      exact e'
  have hex' (U : X.Opens) : Function.Exact ((homMap π (𝟙 G)).app U) ((homMap φ (𝟙 G)).app U) := fun ψ => by
    refine ⟨fun h => exists_hom_of_exact φ π hex hs ψ fun W hW m => ?_, ?_⟩
    · exact congrArg (fun ψ : Γ(homMod Q G, U) => homApp ψ hW m) h
    · rintro ⟨χ, rfl⟩
      refine VB.hom_ext fun W h m => ?_
      rw [homApp_homMap, homApp_homMap, QCoh.app_app φ π, w]
      exact map_zero (homApp χ h)
  have : (homMod F G).IsQuasicoherent :=
    QCoh.isQuasicoherent_of_exact_app (homMap π (𝟙 G)) (homMap φ (𝟙 G)) (fun U _ => hι U) fun U _ => hex' U
  refine .of_forall_exists_affine fun x => ?_
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem x
  have := QCoh.isNoetherian_sections (homMod P G) hU
  exact ⟨U, hU, hx, Module.Finite.of_injective (QCoh.appLinear (homMap π (𝟙 G)) U) (hι U)⟩

theorem isFiniteQC_homMod_cokernel [IsLocallyNoetherian X] {r r' : ℕ} (hQ : IsVB Q r') (hP : IsVB P r) (φ : Q ⟶ P)
    [IsFiniteQC G] : IsFiniteQC (homMod (cokernel φ) G) :=
  have := hQ.isQuasicoherent
  have := hP.isQuasicoherent
  isFiniteQC_homMod_of_exact hQ hP φ (cokernel.π φ) (fun _ hT => QCoh.exact_cokernel_π_app φ hT)
    (fun _ hT => QCoh.surjective_cokernel_π_app φ hT) (cokernel.condition φ)

theorem homOfRestrict_injective {U : X.Opens} :
    Function.Injective (homOfRestrict : (F.restrict U.ι ⟶ G.restrict U.ι) → _) := fun φ ψ e => by
  ext T s
  have h : U.ι ''ᵁ T ≤ U := U.ι_image_le T
  exact (homApp_homOfRestrict_image φ T h s).symm.trans (e ▸ homApp_homOfRestrict_image ψ T h s)

theorem isUnit_natCast_gen (p : ℕ) : IsUnit ((p : ℕ) : Γ((gen X p).toScheme, ⊤)) := by
  have h : IsUnit (resG X (le_top : gen X p ≤ ⊤) ((p : ℕ) : Γ(X, ⊤))) := X.toRingedSpace.isUnit_res_basicOpen _
  have := h.map (gen X p).topIso.inv.hom
  rwa [map_natCast, map_natCast] at this

variable (F) in

def mulNatIso (p : ℕ) : F.restrict (gen X p).ι ≅ F.restrict (gen X p).ι where
  hom := smulHom _ ((p : ℕ) : Γ((gen X p).toScheme, ⊤))
  inv := smulHom _ ((isUnit_natCast_gen p).unit⁻¹ : Γ((gen X p).toScheme, ⊤)ˣ)
  hom_inv_id := by rw [← smulHom_mul, IsUnit.val_inv_mul, smulHom_one]
  inv_hom_id := by rw [← smulHom_mul, IsUnit.mul_val_inv, smulHom_one]

theorem homApp_mulNatIso (p : ℕ) {W : X.Opens} (h : W ≤ gen X p) (s : Γ(F, W)) :
    homApp (homOfRestrict (mulNatIso F p).hom) h s = ((p : ℕ) : Γ(X, W)) • s := by
  have (T : (gen X p).toScheme.Opens) (t : Γ(F.restrict (gen X p).ι, T)) : (mulNatIso F p).hom.app T t = p • t := by
    refine (smulHom_app_apply _ _ T t).trans ?_
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have e (T : (gen X p).toScheme.Opens) (t : Γ(F, (gen X p).ι ''ᵁ T)) : appIm (mulNatIso F p).hom T t = p • t := this T t
  rw [homApp_homOfRestrict, e, map_nsmul, resM_resM, resM_self, Nat.cast_smul_eq_nsmul]

theorem nsmul_id_app (n : ℕ) (U : X.Opens) (s : Γ(F, U)) : (n • 𝟙 F).app U s = n • s := by
  induction n with
  | zero => rw [zero_smul, zero_smul]; rfl
  | succ n ih => rw [succ_nsmul, succ_nsmul, ← ih]; rfl

theorem not_isZero_cokernel_pow {p : ℕ} {C : SCF p} (z : Sp (intO C.S) ⟶ X) (hp : 1 < p) (hF : IsVB F 1) {k : ℕ}
    (hk : k ≠ 0) : ¬ IsZero (cokernel (p ^ k • 𝟙 F)) := fun h₀ => by
  have := isLocalRing_intO C.S
  have := hF.isQuasicoherent
  have : Epi (p ^ k • 𝟙 F) := Preadditive.epi_of_isZero_cokernel _ h₀
  obtain ⟨U, e, hU, hx, -, he⟩ := hF.exists_affine (V := ⊤) (x := z (IsLocalRing.closedPoint _)) trivial
  have h := (top_le_preimage_iff z).2 hx
  obtain ⟨m, hm⟩ := QCoh.surjective_app_of_epi (p ^ k • 𝟙 F) hU (he.basis le_rfl 0)
  have e₁ := congrArg (fun t => ‖((evz z h ((he.basis le_rfl).repr t 0) : intO C.S) : C.S)‖) hm
  simp only [nsmul_id_app, map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_one,
    nsmul_eq_mul, map_mul, map_pow, map_natCast, MulMemClass.coe_mul, OneMemClass.coe_one, norm_one, norm_mul, Nat.cast_pow, SubmonoidClass.coe_pow,
    SubringClass.coe_natCast, norm_pow, C.norm_p] at e₁
  have h₁ : ((p : ℝ)⁻¹) ^ k < 1 := pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)) hk
  exact ((mul_le_of_le_one_right (by positivity) (evz z h _).2).trans_lt h₁).ne e₁

end Coherent

end GlobalTheory.PtNorm

namespace GlobalTheory.LocM

section Reduction

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

abbrev modN (F : 𝒜) (n : ℕ) : 𝒜 := cokernel (n • 𝟙 F)

def modNRed (F : 𝒜) {n m : ℕ} (h : n ∣ m) : modN F m ⟶ modN F n :=
  cokernel.desc _ (cokernel.π _) (by
    obtain ⟨c, rfl⟩ := h
    rw [mul_comm, mul_smul, Preadditive.nsmul_comp, cokernel.condition, smul_zero])

@[reassoc (attr := simp)] theorem π_modNRed (F : 𝒜) {n m : ℕ} (h : n ∣ m) :
    cokernel.π (m • 𝟙 F) ≫ modNRed F h = cokernel.π (n • 𝟙 F) := cokernel.π_desc _ _ _

theorem nsmul_id_modN (F : 𝒜) (n : ℕ) : n • 𝟙 (modN F n) = 0 := by
  rw [← cancel_epi (cokernel.π (n • 𝟙 F)), Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using cokernel.condition (n • 𝟙 F)

def redMap {F G : 𝒜} {n m : ℕ} (h : n ∣ m) (φ : modN F m ⟶ modN G m) : modN F n ⟶ modN G n :=
  cokernel.desc _ (cokernel.π _ ≫ φ ≫ modNRed G h) (by
    rw [Preadditive.nsmul_comp, Category.id_comp, ← Category.comp_id (cokernel.π _ ≫ φ ≫ modNRed G h),
      ← Preadditive.comp_nsmul, nsmul_id_modN, comp_zero])

@[reassoc] theorem modNRed_redMap {F G : 𝒜} {n m : ℕ} (h : n ∣ m) (φ : modN F m ⟶ modN G m) :
    modNRed F h ≫ redMap h φ = φ ≫ modNRed G h := by
  rw [← cancel_epi (cokernel.π (m • 𝟙 F)), π_modNRed_assoc, redMap, cokernel.π_desc]

instance epi_modNRed (F : 𝒜) {n m : ℕ} (h : n ∣ m) : Epi (modNRed F h) :=
  epi_of_epi_fac (π_modNRed F h)

@[simp] theorem redMap_id (F : 𝒜) {n m : ℕ} (h : n ∣ m) : redMap h (𝟙 (modN F m)) = 𝟙 _ := by
  rw [← cancel_epi (modNRed F h), modNRed_redMap, Category.id_comp, Category.comp_id]

theorem redMap_comp {F G H : 𝒜} {n m : ℕ} (h : n ∣ m) (φ : modN F m ⟶ modN G m) (ψ : modN G m ⟶ modN H m) :
    redMap h (φ ≫ ψ) = redMap h φ ≫ redMap h ψ := by
  rw [← cancel_epi (modNRed F h), modNRed_redMap, modNRed_redMap_assoc, modNRed_redMap, Category.assoc]

@[simp] theorem redMap_self {F G : 𝒜} {m : ℕ} (h : m ∣ m) (φ : modN F m ⟶ modN G m) : redMap h φ = φ := by
  have e (F : 𝒜) : modNRed F h = 𝟙 _ := by
    rw [← cancel_epi (cokernel.π (m • 𝟙 F)), π_modNRed, Category.comp_id]
  simpa only [e, Category.id_comp, Category.comp_id] using modNRed_redMap h φ

def modNMap {F G : 𝒜} (φ : F ⟶ G) (n : ℕ) : modN F n ⟶ modN G n :=
  cokernel.map _ _ φ φ (by rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id])

@[reassoc (attr := simp)] theorem π_modNMap {F G : 𝒜} (φ : F ⟶ G) (n : ℕ) :
    cokernel.π (n • 𝟙 F) ≫ modNMap φ n = φ ≫ cokernel.π (n • 𝟙 G) := cokernel.π_desc _ _ _

@[simp] theorem redMap_modNMap {F G : 𝒜} {n m : ℕ} (h : n ∣ m) (φ : F ⟶ G) : redMap h (modNMap φ m) = modNMap φ n := by
  rw [← cancel_epi (modNRed F h), modNRed_redMap, ← cancel_epi (cokernel.π (m • 𝟙 F))]
  simp

theorem exists_shortExact_congr {F G H : 𝒜} {f f' : F ⟶ G} {g g' : G ⟶ H} (hf : f = f') (hg : g = g') :
    (∃ w : f ≫ g = 0, (ShortComplex.mk _ _ w).ShortExact) ↔ ∃ w : f' ≫ g' = 0, (ShortComplex.mk _ _ w).ShortExact := by
  subst hf hg
  rfl

end Reduction

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p) {Z : ct.Mdl}

theorem isVB_free (Z : ct.Mdl) (a m : ℕ) : IsVB (Z.free a m) m :=
  (isVB_freeModule_fin Z.X m).twist (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB _ _ _) _)

instance isFiniteQC_toMod (F : ct.Sh Z) : IsFiniteQC F.toMod :=
  have := (ct.isVB_free Z F.a F.m).isFiniteQC
  have := (ct.isVB_free Z F.a' F.m').isQuasicoherent
  QCoh.isFiniteQC_cokernel F.φ

def presIso (F : Z.X.Modules) [IsFiniteQC F] : (Z.ofMod F).toMod ≅ F :=
  (GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ Z F).some

theorem nrm_eq (F : ct.Sh Z) (f : ct.Sec F) (y : ct.Pt Z) : ct.nrm F f y = sSup (nrmSet y.z F.toMod f) := rfl

theorem nrm_ofMod (F : Z.X.Modules) [IsFiniteQC F] (f : Γ(F, Z.genO)) (y : ct.Pt Z) :
    ct.nrm (Z.ofMod F) ((ct.presIso F).inv.app _ f) y = sSup (nrmSet y.z F f) :=
  congrArg sSup (nrmSet_iso y.z (ct.presIso F).symm f)

theorem isLocallyNoetherian (Z : ct.Mdl) : IsLocallyNoetherian Z.X :=
  have := GlobalTheory.ModelPresentation.isNoetherianRing_place Z.i.c ct.W ct.hp.ne_zero ct.hW
  have : IsProper (PSpace.str (Z.i.c.V ct.W) Z.n) := isProper_str _ _
  LocallyOfFiniteType.isLocallyNoetherian (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V ct.W) Z.n)

instance isFiniteQC_homMod_toMod (F₁ F₂ : ct.Sh Z) : IsFiniteQC (homMod F₁.toMod F₂.toMod) :=
  have := ct.isLocallyNoetherian Z
  isFiniteQC_homMod_cokernel (ct.isVB_free Z F₁.a' F₁.m') (ct.isVB_free Z F₁.a F₁.m) F₁.φ

def isoSymm {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) : ct.GIso F₂ F₁ := φ.symm

def isoRefl (F : ct.Sh Z) (h : ct.IsInv F) : ct.GIso F F := GIso.refl h

def mulP (F : ct.Sh Z) (h : ct.IsInv F) : ct.GIso F F := GIso.mk (mulNatIso F.toMod p) h h

def homSh (F₁ F₂ : ct.Sh Z) : ct.Sh Z := Z.ofMod (homMod F₁.toMod F₂.toMod)

def homIso (F₁ F₂ : ct.Sh Z) : homMod F₁.toMod F₂.toMod ≅ (ct.homSh F₁ F₂).toMod := (ct.presIso _).symm

def isoSec {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) : ct.Sec (ct.homSh F₁ F₂) :=
  (ct.homIso F₁ F₂).hom.app _ (homOfRestrict φ.iso.hom)

theorem exists_homSh_iso (F₁ F₂ : ct.Sh Z) :
    ∃ e : homMod F₁.toMod F₂.toMod ≅ (ct.homSh F₁ F₂).toMod,
      ∀ φ : ct.GIso F₁ F₂, ct.isoSec φ = e.hom.app _ (homOfRestrict φ.iso.hom) :=
  ⟨ct.homIso F₁ F₂, fun _ => rfl⟩

theorem isoSec_injective (F₁ F₂ : ct.Sh Z) : Function.Injective (ct.isoSec : ct.GIso F₁ F₂ → _) := fun _ _ e =>
  GIso.ext (Iso.ext (homOfRestrict_injective (QCoh.injective_app_of_mono (ct.homIso F₁ F₂).hom _ e)))

theorem isVB_homSh {F₁ F₂ : ct.Sh Z} {r : ℕ} (h₁ : ct.IsInv F₁) (h₂ : IsVB F₂.toMod r) :
    IsVB (ct.homSh F₁ F₂).toMod r :=
  (isVB_homMod h₁ h₂).of_iso (ct.homIso F₁ F₂)

theorem homSh_inv (F₁ F₂ : ct.Sh Z) (h₁ : ct.IsInv F₁) (h₂ : ct.IsInv F₂) : ct.IsInv (ct.homSh F₁ F₂) :=
  ct.isVB_homSh h₁ h₂

theorem nrm_isoSec_eq {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y =
      sSup (nrmSet y.z (homMod F₁.toMod F₂.toMod) (compSec (𝟙 _) φ.iso.hom)) :=
  ct.nrm_ofMod _ _ y

theorem nrm_isoSec_pos_symm {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    0 < ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y ∧
      ct.nrm (ct.homSh F₂ F₁) (ct.isoSec (ct.isoSymm φ)) y =
        (ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y)⁻¹ := by
  rw [ct.nrm_isoSec_eq, ct.nrm_isoSec_eq]
  exact sSup_compSec_mul y.z ct.hp.ne_zero φ.isInv_left φ.isInv_right (𝟙 _) (𝟙 _)
    (IsVB.restrict φ.isInv_right _) φ.iso

def vrat {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) : ℝ :=
  -Real.logb p (ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y)

theorem nrm_isoSec {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.nrm (ct.homSh F₁ F₂) (ct.isoSec φ) y = (p : ℝ) ^ (-(ct.vrat φ y)) := by
  rw [vrat, neg_neg, Real.rpow_logb (Nat.cast_pos.2 ct.hp.pos) (by exact_mod_cast ct.hp.one_lt.ne')
    (ct.nrm_isoSec_pos_symm φ y).1]

theorem vrat_symm {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) :
    ct.vrat (ct.isoSymm φ) y = -(ct.vrat φ y) := by
  rw [vrat, vrat, (ct.nrm_isoSec_pos_symm φ y).2, Real.logb_inv]

theorem vrat_refl (F : ct.Sh Z) (h : ct.IsInv F) (y : ct.Pt Z) : ct.vrat (ct.isoRefl F h) y = 0 := by
  have : ct.vrat (ct.isoRefl F h) y = -ct.vrat (ct.isoRefl F h) y := ct.vrat_symm (ct.isoRefl F h) y
  linarith

theorem rpow_neg_vrat {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) {U : Z.X.Opens}
    (h : ⊤ ≤ y.z ⁻¹ᵁ U) {u : Γ(F₁.toMod, U)} {v : Γ(F₂.toMod, U)} (hu : VB.IsFrame fun _ : Fin 1 => u)
    (hv : VB.IsFrame fun _ : Fin 1 => v) (a : Γ(Z.X, U ⊓ Z.genO))
    (ha : homApp (homOfRestrict φ.iso.hom) inf_le_right (resM _ inf_le_left u) = a • resM _ inf_le_left v) :
    (p : ℝ) ^ (-(ct.vrat φ y)) = ‖evq y.z ct.hp.ne_zero h a‖ := by
  rw [← nrm_isoSec, ct.nrm_isoSec_eq]
  exact sSup_compSec_frames y.z ct.hp.ne_zero φ.isInv_left (𝟙 _) (IsVB.restrict φ.isInv_right _) φ.iso h hu hv a ha

theorem vrat_eq_one {F₁ F₂ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (y : ct.Pt Z) {U : Z.X.Opens}
    (h : ⊤ ≤ y.z ⁻¹ᵁ U) {u : Γ(F₁.toMod, U)} {v : Γ(F₂.toMod, U)} (hu : VB.IsFrame fun _ : Fin 1 => u)
    (hv : VB.IsFrame fun _ : Fin 1 => v)
    (ha : homApp (homOfRestrict φ.iso.hom) inf_le_right (resM _ inf_le_left u) =
      ((p : ℕ) : Γ(Z.X, U ⊓ Z.genO)) • resM _ inf_le_left v) : ct.vrat φ y = 1 := by
  have e := (ct.rpow_neg_vrat φ y h hu hv _ ha).trans (congrArg norm (map_natCast (evq y.z ct.hp.ne_zero h) p))
  rw [y.C.norm_p, ← Real.rpow_neg_one] at e
  exact neg_injective ((Real.rpow_right_inj (Nat.cast_pos.2 ct.hp.pos) (by exact_mod_cast ct.hp.one_lt.ne')).1 e)

theorem vrat_mulP (F : ct.Sh Z) (hF : ct.IsInv F) (y : ct.Pt Z) : ct.vrat (ct.mulP F hF) y = 1 := by
  have := isLocalRing_intO y.C.S
  obtain ⟨U, e, hx, he⟩ := hF (y.z (IsLocalRing.closedPoint _))
  have he' : VB.IsFrame fun _ : Fin 1 => e 0 := by rwa [show (fun _ : Fin 1 => e 0) = e from funext fun i => by fin_cases i; rfl]
  exact ct.vrat_eq_one _ y ((top_le_preimage_iff y.z).2 hx) he' he' (homApp_mulNatIso p _ _)

theorem vrat_trans {F₁ F₂ F₃ : ct.Sh Z} (φ : ct.GIso F₁ F₂) (ψ : ct.GIso F₂ F₃) (y : ct.Pt Z) :
    ct.vrat (φ.trans ψ) y = ct.vrat φ y + ct.vrat ψ y := by
  have := isLocalRing_intO y.C.S
  have one {M : Z.X.Modules} {U : Z.X.Opens} {e : Fin 1 → Γ(M, U)} (he : VB.IsFrame e) :
      VB.IsFrame fun _ : Fin 1 => e 0 := by
    rwa [show (fun _ : Fin 1 => e 0) = e from funext fun i => by fin_cases i; rfl]
  have coef {M : Z.X.Modules} {U : Z.X.Opens} {e : Fin 1 → Γ(M, U)} (he : VB.IsFrame e) (t : Γ(M, U ⊓ Z.genO)) :
      ∃ a : Γ(Z.X, U ⊓ Z.genO), t = a • resM M inf_le_left (e 0) :=
    ⟨_, by simpa only [Fin.sum_univ_one, IsFrame.basis_apply] using ((he.basis inf_le_left).sum_repr t).symm⟩
  obtain ⟨U₁, u, hx₁, hu⟩ := φ.isInv_left (y.z (IsLocalRing.closedPoint _))
  obtain ⟨U₂, v, -, hx₂, h₂, hv⟩ := IsVB.exists_affine φ.isInv_right hx₁
  obtain ⟨U, w, -, hx, h₃, hw⟩ := IsVB.exists_affine ψ.isInv_right hx₂
  have h := (top_le_preimage_iff y.z).2 hx
  have hu := hu.res (h₃.trans h₂)
  have hv := hv.res h₃
  obtain ⟨a, ha⟩ := coef hv (homApp (homOfRestrict φ.iso.hom) inf_le_right (resM _ inf_le_left (resM _ (h₃.trans h₂) (u 0))))
  obtain ⟨b, hb⟩ := coef hw (homApp (homOfRestrict ψ.iso.hom) inf_le_right (resM _ inf_le_left (resM _ h₃ (v 0))))
  have e₁ := ct.rpow_neg_vrat φ y h (one hu) (one hv) a ha
  have e₂ := ct.rpow_neg_vrat ψ y h (one hv) (one hw) b hb
  have e₃ := ct.rpow_neg_vrat (φ.trans ψ) y h (one hu) (one hw) (a * b) (by
    rw [GIso.iso_trans, Iso.trans_hom, ← homOfRestrict_comp, ha, map_smul, hb, mul_smul])
  have hp : (0 : ℝ) < p := Nat.cast_pos.2 ct.hp.pos
  have e₄ : (p : ℝ) ^ (-ct.vrat (φ.trans ψ) y) = (p : ℝ) ^ (-(ct.vrat φ y + ct.vrat ψ y)) := by
    rw [neg_add, Real.rpow_add hp, e₁, e₂, e₃, ← norm_mul]
    exact congrArg norm (map_mul (evq y.z ct.hp.ne_zero h) a b)
  exact neg_injective ((Real.rpow_right_inj hp (by exact_mod_cast ct.hp.one_lt.ne')).1 e₄)

def oSh (Z : ct.Mdl) : ct.Sh Z := Z.ofMod (structureModule Z.X)

theorem oSh_inv (Z : ct.Mdl) : ct.IsInv (ct.oSh Z) :=
  (isVB_structureModule Z.X).of_iso (ct.presIso _).symm

def oOne (Z : ct.Mdl) : Γ((ct.oSh Z).toMod, ⊤) := (ct.presIso (structureModule Z.X)).inv.app ⊤ (oneSec ⊤)

theorem isFrame_oOne (Z : ct.Mdl) : VB.IsFrame fun _ : Fin 1 => ct.oOne Z :=
  (isFrame_one ⊤).map_iso (ct.presIso (structureModule Z.X)).inv

def secOf {F : ct.Sh Z} (φ : ct.GIso (ct.oSh Z) F) : ct.Sec F :=
  homApp (homOfRestrict φ.iso.hom) le_rfl (resM _ le_top (ct.oOne Z))

theorem nrm_secOf {F : ct.Sh Z} (φ : ct.GIso (ct.oSh Z) F) (y : ct.Pt Z) :
    ct.nrm F (ct.secOf φ) y = (p : ℝ) ^ (-(ct.vrat φ y)) := by
  rw [← nrm_isoSec, ct.nrm_isoSec_eq]
  exact sSup_compSec_eq y.z ct.hp.ne_zero (ct.oSh_inv Z) (𝟙 _) (ct.isFrame_oOne Z) φ.iso

structure SES (Z : ct.Mdl) : Type where

  F₁ : ct.Sh Z

  F₂ : ct.Sh Z

  F₃ : ct.Sh Z

  k₀ : ℕ

  f : modN F₁.toMod (p ^ k₀) ⟶ modN F₂.toMod (p ^ k₀)

  g : modN F₂.toMod (p ^ k₀) ⟶ modN F₃.toMod (p ^ k₀)

variable {ct}

def SES.ExactMod (s : ct.SES Z) (k : ℕ) : Prop :=
  ∃ (h : k ≤ s.k₀) (w : redMap (pow_dvd_pow p h) s.f ≫ redMap (pow_dvd_pow p h) s.g = 0),
    (ShortComplex.mk _ _ w).ShortExact

def SES.ofMaps {F₁ F₂ F₃ : ct.Sh Z} (f : F₁.toMod ⟶ F₂.toMod) (g : F₂.toMod ⟶ F₃.toMod) (k₀ : ℕ) : ct.SES Z :=
  ⟨F₁, F₂, F₃, k₀, modNMap f _, modNMap g _⟩

theorem SES.exactMod_ofMaps_iff {F₁ F₂ F₃ : ct.Sh Z} (f : F₁.toMod ⟶ F₂.toMod) (g : F₂.toMod ⟶ F₃.toMod) {k k₀ : ℕ}
    (h : k ≤ k₀) : (SES.ofMaps f g k₀).ExactMod k ↔
      ∃ w : modNMap f (p ^ k) ≫ modNMap g (p ^ k) = 0, (ShortComplex.mk _ _ w).ShortExact :=
  (exists_prop_of_true h).trans (exists_shortExact_congr (redMap_modNMap _ _) (redMap_modNMap _ _))

theorem SES.exactMod_self_iff (s : ct.SES Z) :
    s.ExactMod s.k₀ ↔ ∃ w : s.f ≫ s.g = 0, (ShortComplex.mk _ _ w).ShortExact :=
  (exists_prop_of_true le_rfl).trans (exists_shortExact_congr (redMap_self _ _) (redMap_self _ _))

theorem SES.exactMod_of_splitting {F₁ F₂ F₃ : ct.Sh Z} {f : F₁.toMod ⟶ F₂.toMod} {g : F₂.toMod ⟶ F₃.toMod}
    {w : f ≫ g = 0} (σ : (ShortComplex.mk f g w).Splitting) {k k₀ : ℕ} (h : k ≤ k₀) :
    (SES.ofMaps f g k₀).ExactMod k := by
  rw [SES.exactMod_ofMaps_iff f g h]
  refine ⟨?_, ShortComplex.Splitting.shortExact
    { r := modNMap σ.r _, s := modNMap σ.s _, f_r := ?_, s_g := ?_, id := ?_ }⟩ <;>
    rw [← cancel_epi (cokernel.π _)]
  · simp [reassoc_of% w]
  · have := σ.f_r
    dsimp at this ⊢
    simp [reassoc_of% this]
  · have := σ.s_g
    dsimp at this ⊢
    simp [reassoc_of% this]
  · have := σ.id =≫ cokernel.π (p ^ k • 𝟙 F₂.toMod)
    dsimp at this ⊢
    simpa using this

def SES.sum (F G : ct.Sh Z) (k₀ : ℕ) : ct.SES Z :=
  SES.ofMaps (F₁ := F) (F₂ := Z.ofMod (F.toMod ⊞ G.toMod)) (F₃ := G)
    (biprod.inl ≫ (ct.presIso (F.toMod ⊞ G.toMod)).inv) ((ct.presIso (F.toMod ⊞ G.toMod)).hom ≫ biprod.snd) k₀

theorem SES.exactMod_sum (F G : ct.Sh Z) {k k₀ : ℕ} (h : k ≤ k₀) : (SES.sum F G k₀).ExactMod k :=
  SES.exactMod_of_splitting (w := by simp)
    { r := (ct.presIso (F.toMod ⊞ G.toMod)).hom ≫ biprod.fst
      s := biprod.inr ≫ (ct.presIso (F.toMod ⊞ G.toMod)).inv
      f_r := by simp
      s_g := by simp
      id := by
        have := (ct.presIso (F.toMod ⊞ G.toMod)).hom ≫= (biprod.total =≫ (ct.presIso (F.toMod ⊞ G.toMod)).inv)
        simpa only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Category.id_comp,
          Iso.hom_inv_id] using this } h

theorem SES.isZero_of_exactMod_zero {F₁ F₂ F₃ : ct.Sh Z} {k : ℕ}
    (h : (⟨F₁, F₂, F₃, k, 0, 0⟩ : ct.SES Z).ExactMod k) : IsZero (modN F₂.toMod (p ^ k)) := by
  obtain ⟨w, hw⟩ := (SES.exactMod_self_iff _).1 h
  exact hw.exact.isZero_X₂ rfl rfl

theorem SES.not_exactMod_zero {F₁ F₂ F₃ : ct.Sh Z} (h : ct.IsInv F₂) (y : ct.Pt Z) {k : ℕ} (hk : k ≠ 0) :
    ¬ (⟨F₁, F₂, F₃, k, 0, 0⟩ : ct.SES Z).ExactMod k := fun h' =>
  not_isZero_cokernel_pow y.z ct.hp.one_lt h hk (SES.isZero_of_exactMod_zero h')

end At

def shfTrue (ct : At S κ p) : ShfSt ct where
  vrat := ct.vrat
  SES := ct.SES
  ExactMod := At.SES.ExactMod
  homSh := ct.homSh
  homSh_inv := ct.homSh_inv
  isoSec := ct.isoSec
  nrm_isoSec := ct.nrm_isoSec
  isoSymm := ct.isoSymm
  vrat_symm := ct.vrat_symm
  oX := ct.oSh ct.Xm
  oX_inv := ct.oSh_inv _
  secOf := ct.secOf
  nrm_secOf := ct.nrm_secOf

example (ct : At S κ p) {Z : ct.Mdl} (F : ct.Sh Z) (h : ct.IsInv F) (y : ct.Pt Z) :
    (shfTrue ct).vrat (ct.isoRefl F h) y = 0 :=
  ct.vrat_refl F h y

example (ct : At S κ p) (y : ct.Pt ct.Xm) :
    ct.nrm (ct.oSh ct.Xm) ((shfTrue ct).secOf (ct.mulP (ct.oSh ct.Xm) (ct.oSh_inv _))) y = (p : ℝ)⁻¹ :=
  (ct.nrm_secOf _ y).trans (by rw [ct.vrat_mulP, Real.rpow_neg_one])

example (ct : At S κ p) (y : ct.Pt ct.Xm) :
    ct.nrm (ct.oSh ct.Xm) ((shfTrue ct).secOf (ct.isoRefl (ct.oSh ct.Xm) (ct.oSh_inv _))) y = 1 :=
  (ct.nrm_secOf _ y).trans (by rw [ct.vrat_refl, neg_zero, Real.rpow_zero])

example (ct : At S κ p) {Z : ct.Mdl} (F G : ct.Sh Z) (hG : IsZero G.toMod) (k : ℕ) :
    (shfTrue ct).ExactMod (At.SES.ofMaps (𝟙 F.toMod) (0 : F.toMod ⟶ G.toMod) k) k :=
  At.SES.exactMod_of_splitting (w := comp_zero)
    { r := 𝟙 _, s := 0, f_r := Category.id_comp _, s_g := hG.eq_of_src _ _, id := by simp } le_rfl

end GlobalTheory.LocM
