import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesMatrixActionFreeModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorThroughMonoLocalLiftsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMatrixActionCoordinatesStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc

theorem exists_fac_of_latOf_le {X : Scheme.{0}} {h : ℕ} {F E : X.Modules} [F.IsQuasicoherent] [E.IsQuasicoherent]
    (u : F ⟶ freeModule X (Fin h)) (ι : E ⟶ freeModule X (Fin h)) [Mono ι] {I : Type} {V : I → X.Opens}
    (h1 : ∀ i, IsAffineOpen (V i)) (h2 : ∀ x : X, ∃ i, x ∈ V i) (h3 : ∀ i, latOf u (V i) ≤ latOf ι (V i)) :
    ∃ v : F ⟶ E, v ≫ ι = u := by
  haveI := (GlobalTheory.VB.isVB_freeModule_fin (X := X) h).isQuasicoherent
  refine GlobalTheory.T.factor_through_mono_local_lifts X F E _ u ι I V h1 h2 fun i s => ?_
  obtain ⟨s', hs'⟩ := h3 i ⟨s, rfl⟩
  exact ⟨s', (GlobalTheory.LatGlue.coords X h (V i)).injective hs'⟩

theorem latOf_smulHom {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : GlobalTheory.Vert.Model O} (h : ℕ)
    (π : Γ(B.X, ⊤)) (W : B.X.Opens) : latOf (smulHom (freeModule B.X (Fin h)) π) W = baseOn h π W := by
  have key : ∀ s, crd (smulHom (freeModule B.X (Fin h)) π) W s = resG B.X le_top π • GlobalTheory.LatGlue.coords B.X h W s :=
    fun s => (GlobalTheory.LatGlue.coords B.X h W).map_smul _ s
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, trivial, (key s).symm⟩
  · rintro ⟨y, -, rfl⟩
    obtain ⟨s, rfl⟩ := (GlobalTheory.LatGlue.coords B.X h W).surjective y
    exact ⟨s, key s⟩

theorem isIso_genRes_map_smulHom_of_root {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    {p : ℕ} [Fact p.Prime] {B : GlobalTheory.Vert.Model O} (F : B.X.Modules) {π : Γ(B.X, ⊤)} (hπ : IsRootOfP p π (p - 1)) :
    IsIso (B.genRes.map (smulHom F π)) := by
  rw [GlobalTheory.VB.pullback_map_smulHom]
  obtain ⟨u, hu⟩ := hπ
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hg : (p : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h : IsUnit (B.gen.ι.appTop (B.const (p : O))) :=
    RingedSpace.isUnit_of_isUnit_germ _ _ _ fun x _ => (Scheme.mem_basicOpen_top _ _ x).1
      ((Scheme.preimage_basicOpen_top B.gen.ι _).le (B.gen_le_basicOpen hg x.2))
  have e : B.const (p : O) = (p : Γ(B.X, ⊤)) := map_natCast _ _
  rw [e] at h
  have h' : IsUnit (B.gen.ι.appTop π) := by
    rw [← isUnit_pow_iff (n := p - 1) (by omega), ← map_pow, hu, map_mul]
    exact (u.isUnit.map _).mul h
  exact (isUnit_iff_isIso _).1 (h'.map (smulEnd _))

theorem exists_action_of_fac {X : Scheme.{0}} {Λ : Type} [CommRing Λ] {E G : X.Modules} (ι : E ⟶ G) [Mono ι]
    (μ : Λ →+* End G) (hs : ∀ a, ∃ v : E ⟶ E, v ≫ ι = ι ≫ (μ a : G ⟶ G)) :
    ∃ ρ : Λ →* End E, (∀ a b, (ρ (a + b) : E ⟶ E) = (ρ a : E ⟶ E) + (ρ b : E ⟶ E)) ∧
      ∀ a, (ρ a : E ⟶ E) ≫ ι = ι ≫ (μ a : G ⟶ G) := by
  choose v hv using hs
  refine ⟨⟨⟨v, ?_⟩, fun a b => ?_⟩, fun a b => ?_, hv⟩
  · change v 1 = 𝟙 E
    rw [← cancel_mono ι, hv, map_one, Category.id_comp]
    exact Category.comp_id _
  · change v (a * b) = v b ≫ v a
    rw [← cancel_mono ι, hv, map_mul, Category.assoc, hv, ← Category.assoc, hv, Category.assoc]
    rfl
  · change v (a + b) = v a + v b
    rw [← cancel_mono ι, hv, map_add, Preadditive.add_comp, hv, hv, ← Preadditive.comp_add]

theorem exists_presentations_of_isLoc : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)), [CharZero O] → IsRootOfP p π (p - 1) → IsLoc M ι V D → ∃ (q l : ℕ → EPres B Λ) (tq : ∀ n, E n ⟶ (q n).mod.V) (tl : ∀ n, E n ⟶ (l n).mod.V), (∀ n ≤ o, IsQuot M (ι n) (baseOn h π) (q n).mod (tq n)) ∧ (∀ n < o, IsQuot M (ι n) (latOf (ι (n + 1))) (l n).mod (tl n)) ∧ ∀ n < o, IsExtA (q (n + 1)).mod (q n).mod (l n).mod := by
  intro O _ _ _ p _ B Λ _ h o Lie Om π γ M E ι I V D _ hπ hL
  obtain ⟨h1, h2, -, hE, hF, -, hM⟩ := hL
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.coordinates_matrix_action_free_module B.X h
  have vbT := GlobalTheory.VB.isVB_freeModule_fin (X := B.X) h
  haveI := vbT.isQuasicoherent
  haveI := fun n => (hE n).1.isQuasicoherent
  haveI := fun n => (hE n).2
  have hρ := fun n (hn : n ≤ o) => exists_action_of_fac (ι n) (μ.comp M) fun a =>
    exists_fac_of_latOf_le _ (ι n) h1 h2 fun i => by
      rintro _ ⟨s, rfl⟩
      have := (hM i a).mem n _ ((hF i n hn).ge ⟨s, rfl⟩)
      rw [hF i n hn] at this
      exact (hμ (M a) (V i) ((ι n).app _ s)) ▸ this
  choose ρ ρadd ρι using hρ
  have ha := fun n (hn : n ≤ o) => exists_fac_of_latOf_le (smulHom (freeModule B.X (Fin h)) π) (ι n) h1 h2 fun i => by
    rw [latOf_smulHom, ← hF i n hn]; exact (D i).base_le n
  choose a ha using ha
  have hb := fun n (hn : n < o) => exists_fac_of_latOf_le (ι (n + 1)) (ι n) h1 h2 fun i => by
    rw [← hF i n hn.le, ← hF i (n + 1) hn]; exact (D i).succ_le n
  choose b hb using hb
  let T : AM B Λ := ⟨freeModule B.X (Fin h), (μ.comp M).toMonoidHom⟩
  let H : ∀ n ≤ o, AM B Λ := fun n hn => ⟨E n, ρ n hn⟩
  have addT : IsAdd T := fun x y => map_add (μ.comp M) x y
  let A : ∀ n hn, T ⟶ H n hn := fun n hn => ⟨a n hn, fun c => by
    change ((μ.comp M) c : freeModule B.X (Fin h) ⟶ _) ≫ a n hn = a n hn ≫ (ρ n hn c : E n ⟶ E n)
    rw [← cancel_mono (ι n), Category.assoc, Category.assoc, ρι, ← Category.assoc (a n hn), ha]
    first | exact (smulHom_comp _ _).symm | exact smulHom_comp _ _⟩
  let Bm : ∀ n (hn : n < o), H (n + 1) hn ⟶ H n hn.le := fun n hn => ⟨b n hn, fun c => by
    change (ρ (n + 1) hn c : E (n + 1) ⟶ _) ≫ b n hn = b n hn ≫ (ρ n hn.le c : E n ⟶ E n)
    rw [← cancel_mono (ι n), Category.assoc, Category.assoc, ρι, ← Category.assoc (b n hn), hb, ρι]⟩
  have iπ := isIso_genRes_map_smulHom_of_root (freeModule B.X (Fin h)) hπ
  have iι : ∀ n ≤ o, IsIso (B.genRes.map (ι n)) := fun n hn => by
    haveI : Mono (B.genRes.map (ι n)) := mono_pullback_map _ _
    haveI : Epi (B.genRes.map (a n hn) ≫ B.genRes.map (ι n)) := by rw [← Functor.map_comp, ha]; infer_instance
    haveI := epi_of_epi (B.genRes.map (a n hn)) (B.genRes.map (ι n))
    exact isIso_of_mono_of_epi _
  have ia : ∀ n hn, IsIso (B.genRes.map (a n hn)) := fun n hn => by
    haveI := iι n hn
    haveI : IsIso (B.genRes.map (a n hn) ≫ B.genRes.map (ι n)) := by rw [← Functor.map_comp, ha]; infer_instance
    exact IsIso.of_isIso_comp_right _ (B.genRes.map (ι n))
  have ib : ∀ n hn, IsIso (B.genRes.map (b n hn)) := fun n hn => by
    haveI := iι n hn.le
    haveI := iι (n + 1) hn
    haveI : IsIso (B.genRes.map (b n hn) ≫ B.genRes.map (ι n)) := by rw [← Functor.map_comp, hb]; infer_instance
    exact IsIso.of_isIso_comp_right _ (B.genRes.map (ι n))
  have act : ∀ n hn (c : Λ) (W : B.X.Opens) (s : Γ(E n, W)),
      crd (ι n) W ((ρ n hn c : E n ⟶ E n).app W s) = mv (RingHom.id _) (M c) (crd (ι n) W s) := fun n hn c W s =>
    (congrArg (fun φ => crd φ W s) (ρι n hn c)).trans (hμ (M c) W ((ι n).app W s))
  let d : EPres B Λ := ⟨h, T, T, addT, addT, vbT, vbT, smulA T π, iπ⟩
  let q' : ∀ n ≤ o, Σ P : EPres B Λ, E n ⟶ P.mod.V := fun n hn =>
    ⟨⟨h, H n hn, T, ρadd n hn, addT, (hE n).1, vbT, A n hn, ia n hn⟩, (cokernel.π (A n hn)).hom⟩
  let l' : ∀ n < o, Σ P : EPres B Λ, E n ⟶ P.mod.V := fun n hn =>
    ⟨⟨h, H n hn.le, H (n + 1) hn, ρadd n hn.le, ρadd (n + 1) hn, (hE n).1, (hE (n + 1)).1, Bm n hn, ib n hn⟩,
      (cokernel.π (Bm n hn)).hom⟩
  obtain ⟨q, hq⟩ : ∃ q : ∀ n, Σ P : EPres B Λ, E n ⟶ P.mod.V, ∀ n hn, q n = q' n hn :=
    ⟨fun n => if hn : n ≤ o then q' n hn else ⟨d, 0⟩, fun n hn => dif_pos hn⟩
  obtain ⟨l, hl⟩ : ∃ l : ∀ n, Σ P : EPres B Λ, E n ⟶ P.mod.V, ∀ n hn, l n = l' n hn :=
    ⟨fun n => if hn : n < o then l' n hn else ⟨d, 0⟩, fun n hn => dif_pos hn⟩
  refine ⟨fun n => (q n).1, fun n => (l n).1, fun n => (q n).2, fun n => (l n).2, fun n hn => ?_, fun n hn => ?_,
    fun n hn => ?_⟩
  · have k := GlobalTheory.T.quotient_matrix_action_coordinates O B Λ h M (H n hn) T (ι n) (A n hn) (act n hn)
    have e : (fun W => latOf ((A n hn).hom ≫ ι n) W) = baseOn h π := funext fun W => by
      rw [← latOf_smulHom, ← ha n hn]
    rw [e] at k
    beta_reduce
    rw [hq n hn]
    exact k
  · have k := GlobalTheory.T.quotient_matrix_action_coordinates O B Λ h M (H n hn.le) (H (n + 1) hn) (ι n) (Bm n hn) (act n hn.le)
    have e : (fun W => latOf ((Bm n hn).hom ≫ ι n) W) = latOf (ι (n + 1)) := funext fun W => by
      rw [← hb n hn]
    rw [e] at k
    beta_reduce
    rw [hl n hn]
    exact k
  · beta_reduce
    rw [hq n hn.le, hq (n + 1) hn, hl n hn]
    haveI : Mono (b n hn ≫ ι n) := by rw [hb]; infer_instance
    haveI : Mono (Bm n hn) := (Action.forget _ Λ).mono_of_mono_map (mono_of_mono (b n hn) (ι n))
    refine ⟨_, shortExact_cokernel_comp (A (n + 1) hn) (Bm n hn), ⟨Iso.refl _⟩, ⟨cokernelIsoOfEq ?_⟩, ⟨Iso.refl _⟩⟩
    apply Action.Hom.ext
    change a (n + 1) hn ≫ b n hn = a n hn.le
    rw [← cancel_mono (ι n), Category.assoc, hb, ha, ha]

end GlobalTheory.ChainDesc
