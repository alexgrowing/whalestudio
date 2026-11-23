import Development.EtaleCohomology.EtaleSheaves.LeafExtTensPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensMonoPf
open LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp [Sec.res]

theorem loc_trans {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let T : ∀ ⦃V : Scheme.{0}⦄ ⦃f : V ⟶ U⦄, S.arrows f → Sieve V := fun V f hf =>
    Classical.choose (hPQ V f (hP V f hf))
  refine ⟨Sieve.bind S.arrows T, (Scheme.etaleTopology.{0}).bind_covering hS
    (fun V f hf => (Classical.choose_spec (hPQ V f (hP V f hf))).1), ?_⟩
  rintro W _ ⟨V, k, f, hf, hk, rfl⟩
  exact (Classical.choose_spec (hPQ V f (hP V f hf))).2 W k hk

theorem eq_zero_of_loc {F : Shv R} {U : Scheme.{0}} (y : Sec F U) (h : Loc U fun _ g => Sec.res g y = 0) : y = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  let e : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have := F.property.hom_ext ⟨S, hS⟩ e 0 (fun I => by
    ext1; apply LinearMap.ext_ring
    have := hP _ I.f I.hf
    simpa [e] using this)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) 1
  simpa [e] using h2

theorem mono_of_loc {F G : Shv R} (f : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = 0 → Loc U fun _ g => Sec.res g y = 0) : Mono f := by
  have : Mono ((sheafToPresheaf _ _).map f) := by
    have hm : ∀ U, Mono (((sheafToPresheaf Scheme.etaleTopology (ModuleCat (ULift.{1, 0} R))).map f).app U) := by
      intro U
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro y hy
      exact eq_zero_of_loc y (h U.unop y hy)
    exact NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem lift_res {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift, Tens.res]
    exact (μ.nat g _ _ _ p.2 a b).symm
  exact LinearMap.congr_fun this x

theorem lift_compat {I J K K' : Cx R} (σ : Pair I J K) (ν : Pair I J K') (ι : K ⟶ K')
    (h : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (ι.f w) (σ.mul U s t w hw a b) = ν.mul U s t w hw a b) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map (ι.f w) (σ.lift U w x) = ν.lift U w x := by
  have : ((ι.f w).hom.app (op U)).hom.comp (σ.lift U w) = ν.lift U w := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift]
    exact h U _ _ _ p.2 a b
  exact LinearMap.congr_fun this x
end

def LeafTw0LocSplit : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec ((sgl (tw q 0)).X 0) U),
  Loc U fun V g => ∃ (e : Sec ((sgl (tw q 0)).X 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧
    (e = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      r (Sec.map ((resAug (tw q 0)).f 0) e) = 1)

def LeafPreTensLocInj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T),
  τ.IsTensor → ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens (sgl (tw q 0)) (res _ (tw q i)) U w),
  (pre τ (resAug (tw q 0))).lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

theorem LeafTensMono_of (hL : LeafPreTensLocInj) : LateralTheory.E.LeafExtTensPf.LeafTensMono := by
  intro q _ i S T σ τ hσ hτ ι hι n
  apply mono_of_loc
  intro U y hy
  have hc := lift_compat σ (pre τ (resAug (tw q 0))) ι (fun U s t w hw a b => hι U s t w hw a b)
  refine loc_trans (hσ.1 U n y) ?_
  rintro V g ⟨x, hx⟩
  have h0 : (pre τ (resAug (tw q 0))).lift V n x = 0 := by
    rw [← hc, hx, ← res_map, hy]; simp
  obtain ⟨S', hS', hP'⟩ := hL q i τ hτ V n x h0
  exact ⟨S', hS', fun W k hk => by
    show Sec.res (k ≫ g) y = 0
    have hk' : Tens.res k n x = 0 := hP' W k hk
    rw [res_comp, ← hx, ← lift_res, hk', map_zero]⟩

end LateralTheory.E.LeafTensMonoPf
