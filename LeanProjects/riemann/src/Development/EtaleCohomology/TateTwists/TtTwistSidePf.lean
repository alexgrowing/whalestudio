import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS
import Development.EtaleCohomology.TateTwists.EtaleTensorHomDescendsAlongTensorPairing

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.TwSide

def tw_mul : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ)

def tw_flat : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i)

def flip_ex : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), ∃ ν : Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧ (μ.IsTensor → ν.IsTensor)

def tens_qis : Prop := ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

variable {R : Type} [CommRing R]

theorem sec_sub {F : Shv R} (h : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor; intro a b
  have : 𝟙 F = 0 := h.eq_of_src _ _
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, this]; rfl

theorem flat_zero {F : Shv R} (h : IsZero F) : FlatS F := by
  refine ⟨F.obj, 𝟙 _, fun U y => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => ⟨Sec.res g y, rfl⟩,
    fun U x _ => LateralTheory.EtaleFoundations.TensFam.loc_top fun V g => @Subsingleton.elim _ (sec_sub h V) _ _, fun U _ => ?_⟩
  haveI := sec_sub h U
  infer_instance

open ZeroObject in
theorem flat_sgl {F : Shv R} (hF : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact (show FlatS (if (0:ℤ) = 0 then F else 0) by rw [if_pos rfl]; exact hF)
  · exact flat_zero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

theorem sgl_sub (F : Shv R) {t : ℤ} (ht : t ≠ 0) (U : Scheme.{0}) : Subsingleton (Sec ((sgl F).X t) U) :=
  sec_sub (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht) U

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) (φ.hom.naturality g.op)).symm

theorem map_comp' {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_zero' {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem tens_ind {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (P : Tens I J U w → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (ht : ∀ p a b, P (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b))) (x : Tens I J U w) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd _ _ hx hy
  | of p z =>
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => simpa [DirectSum.lof_eq_of] using ht p a b
    | add z1 z2 h1 h2 => rw [map_add]; exact hadd _ _ h1 h2

theorem lift_lof {I J K : Cx R} (τ : Pair I J K) (U : Scheme.{0}) (w : ℤ) p a b :
    τ.lift U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) = τ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [Pair.lift, DirectSum.toModule_lof]

theorem shv_isZero {F : Shv R} (h : ∀ U : Scheme.{0}, ∀ y : Sec F U, y = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact h _ y

end LateralTheory.EtaleFoundations.TwSide

namespace LateralTheory.EtaleFoundations.TwSide
variable {q : ℕ} [NeZero q]

noncomputable def T {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) :
    Tens A B U w →ₗ[ULift.{1} (ZMod q)] Tens A J U w :=
  DirectSum.toModule _ _ _ fun p => (DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = w}
      (fun p => Sec (A.X p.1.1) U ⊗[ULift.{1} (ZMod q)] Sec (J.X p.1.2) U) p).comp
    (TensorProduct.map LinearMap.id ((ε.f p.1.2).hom.app (op U)).hom)

theorem T_lof {A B J : Cx (ZMod q)} (ε : B ⟶ J) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (A.X p.1.1) U) (b : Sec (B.X p.1.2) U) :
    T ε U w (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ Sec.map (ε.f p.1.2) b) := by
  simp [T, DirectSum.toModule_lof]

theorem smul_eq (c : ULift.{1} (ZMod q)) : c = ((c.down.val : ℕ) : ULift.{1} (ZMod q)) := by
  apply ULift.ext; rw [ULift.down_natCast, ZMod.natCast_zmod_val]

noncomputable def ofFam {F G : Shv (ZMod q)} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hφ : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := map_add _
          map_smul' := fun c y => by
            rw [smul_eq c]
            simp only [Nat.cast_smul_eq_nsmul, map_nsmul, RingHom.id_apply] }
      naturality := fun U V g => by
        ext y
        exact (hφ V.unop U.unop g.unop y).symm }

theorem twist_side (htm : tw_mul) (htf : tw_flat) (hfl : flip_ex) (hqis : tens_qis) (i j k : ℤ) (hk : i + j = k)
    {J M : Cx (ZMod q)} (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U) (hJ : IsTwRes q j J e')
    (hflat : ∀ t, FlatS (J.X t)) (σ : Pair (sgl (tw q i)) J M) (hσ : σ.IsTensor) :
    IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ) := by
  obtain ⟨μ, hμ, hgen⟩ := htm q i j k hk
  obtain ⟨hJge, ε', hε', hε'gen⟩ := hJ

  have hMge : M.IsStrictlyGE 0 := by
    refine (CochainComplex.isStrictlyGE_iff M 0).2 fun w hw => shv_isZero fun U y => ?_
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hσ.1 U w y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [← hx, show Sec.res g (0 : Sec (M.X w) U) = 0 from map_zero _]
    refine tens_ind (fun x => σ.lift V w x = 0) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
      (fun p a b => ?_) x
    rw [lift_lof]
    rcases p with ⟨⟨s, t⟩, hst⟩
    by_cases hs : s = 0
    · have ht : t < 0 := by simp only at hst; omega
      haveI := sec_sub (CochainComplex.isZero_of_isStrictlyGE J 0 t (by omega)) V
      rw [Subsingleton.elim b 0, map_zero]
    · haveI := sgl_sub (tw q i) hs V
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
  let b : ∀ U : Scheme.{0}, Tens (sgl (tw q i)) (sgl (tw q j)) U 0 →+ Sec (M.X 0) U :=
    fun U => ((σ.lift U 0).comp (T ε' U 0)).toAddMonoidHom
  have hbv : ∀ U p a c, b U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ p (a ⊗ₜ c)) =
      σ.mul U p.1.1 p.1.2 0 p.2 a (Sec.map (ε'.f p.1.2) c) := by
    intro U p a c
    simp only [b, LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, T_lof, lift_lof]
  have hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g 0 x) := by
    intro V U g x
    refine tens_ind (fun x => Sec.res g (b U x) = b V (Tens.res g 0 x)) (by simp)
      (fun x y hx hy => by simp only [map_add, hx, hy]) (fun p a c => ?_) x
    rw [hbv, σ.nat, map_res]
    simp only [Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul]
    rw [hbv]
  obtain ⟨φ, hφnat, hφlift⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing (ZMod q) (ZMod q) μ hμ 0 (M.X 0) b hb
  have hd : ∀ U (y : Sec ((sgl (tw q k)).X 0) U), Sec.map (M.d 0 (0 + 1)) (φ U y) = 0 := by
    intro U y
    apply LateralTheory.EtaleFoundations.TensFam.sep
    obtain ⟨S, hS, h1⟩ := hμ.1 U 0 y
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := h1 V g hg
    rw [show Sec.res g (0 : Sec (M.X (0 + 1)) U) = 0 from map_zero _, map_res, hφnat, ← hx, hφlift]
    refine tens_ind (fun x => Sec.map (M.d 0 (0 + 1)) (b V x) = 0) (by simp)
      (fun x y hx hy => by simp only [map_add, hx, hy, add_zero]) (fun p a c => ?_) x
    rcases p with ⟨⟨s, t⟩, hst⟩
    rw [hbv]
    have hl := σ.leibniz V s t 0 hst a (Sec.map (ε'.f t) c)
    have hz : ∀ (F : Shv (ZMod q)) (m n : ℤ), (sgl F).d m n = 0 := fun F m n => HomologicalComplex.single_obj_d _ _ _ _ _
    rw [hl, ← map_comp', ε'.comm, map_comp', hz, hz]
    simp only [map_zero', map_zero, LinearMap.zero_apply, smul_zero, add_zero]
  let u : sgl (tw q k) ⟶ M := HomologicalComplex.mkHomFromSingle (sglι (tw q k) ≫ ofFam φ hφnat) (by
    intro l hl
    obtain rfl : l = 0 + 1 := by simp at hl; omega
    ext U y
    exact hd _ _)
  have hu0 : ∀ U (z : Sec ((sgl (tw q k)).X 0) U), Sec.map (u.f 0) z = φ U z := by
    intro U z
    rw [HomologicalComplex.mkHomFromSingle_f, ← Category.assoc]
    show Sec.map (ofFam φ hφnat) (Sec.map ((HomologicalComplex.singleObjXSelf _ 0 (tw q k)).hom ≫ (HomologicalComplex.singleObjXSelf _ 0 (tw q k)).inv) z) = _
    rw [Iso.hom_inv_id]; rfl
  have cmp : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q i)).X s) U) (c : Sec ((sgl (tw q j)).X t) U),
      Sec.map (u.f w) (μ.mul U s t w h a c) = σ.mul U s t w h a (Sec.map (ε'.f t) c) := by
    intro U s t w h a c
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · subst hs ht
        obtain rfl : w = 0 := by omega
        rw [hu0]
        have := hφlift U (DirectSum.lof (ULift.{1} (ZMod q)) _ _ ⟨(0,0), h⟩ (a ⊗ₜ c))
        rw [lift_lof] at this
        rw [this, hbv]
      · haveI := sgl_sub (tw q j) ht U
        rw [Subsingleton.elim c 0]
        simp only [map_zero]
    · haveI := sgl_sub (tw q i) hs U
      rw [Subsingleton.elim a 0]
      simp only [map_zero, LinearMap.zero_apply]
  obtain ⟨μf, hμf, -, hμfT⟩ := hfl (ZMod q) μ
  obtain ⟨σf, hσf, -, hσfT⟩ := hfl (ZMod q) σ
  haveI := hJge
  haveI := hε'
  have hcomp : μf.Compat σf ε' (𝟙 _) u := by
    intro U s t w h a c
    rw [HomologicalComplex.id_f]
    show _ = σf.mul U s t w h (Sec.map (ε'.f s) a) c
    rw [hμf U t s w (by omega) c a, hσf U t s w (by omega) c _, Units.smul_def, Units.smul_def, ← cmp]
    exact map_zsmul ((u.f w).hom.app (op U)).hom _ _
  have hu : QuasiIso u := hqis (ZMod q) μf σf (hμfT hμ) (hσfT hσ) (flat_sgl (htf q i)) ε' u hcomp
  refine ⟨hMge, u, hu, fun U ζ => ?_⟩
  rw [← hgen U ζ, cmp, hε'gen]

end LateralTheory.EtaleFoundations.TwSide

theorem LateralTheory.EtaleFoundations.tt_twist_side_of (htm : LateralTheory.EtaleFoundations.TwSide.tw_mul) (htf : LateralTheory.EtaleFoundations.TwSide.tw_flat)
    (hfl : LateralTheory.EtaleFoundations.TwSide.flip_ex) (hqis : LateralTheory.EtaleFoundations.TwSide.tens_qis) : LateralTheory.EtaleFoundations.tt_twist_side := by
  intro q _ i j k hk J M e' hJ hflat σ hσ
  exact LateralTheory.EtaleFoundations.TwSide.twist_side htm htf hfl hqis i j k hk e' hJ hflat σ hσ
