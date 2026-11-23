import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem trS_map_iso {X : Scheme.{0}} {M M' : X.Modules} {r : ℕ} (φ : M ≅ M') (c c' : Chart M r) :
    trS (c.map φ) (c'.map φ) = trS c c' := by
  ext a b : 1
  have h₁ : c.U ⊓ c'.U ≤ c.U := inf_le_left
  have h₂ : c.U ⊓ c'.U ≤ c'.U := inf_le_right
  have key : ∀ t : Γ(M, c.U ⊓ c'.U), (((c.isFrame.map_iso φ.hom).basis h₁).repr (φ.hom.app _ t)) =
      (c.isFrame.basis h₁).repr t := fun t => by
    conv_lhs => rw [← (c.isFrame.basis h₁).sum_repr t]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, IsFrame.basis_apply, Twist.app_resM]
    simp only [← (c.isFrame.map_iso φ.hom).basis_apply h₁]
    rw [← map_sum]
    ext k
    exact congrFun (((c.isFrame.map_iso φ.hom).basis h₁).repr_sum_self _) k
  have := key (Twist.resM M h₂ (c'.e b))
  rw [Twist.app_resM] at this
  exact congrArg (fun t => t a) this

private theorem trAt_map_iso {X : Scheme.{0}} {M M' : X.Modules} {r : ℕ} {K : Type} [CommRing K] (x : Sp K ⟶ X)
    (φ : M ≅ M') (c c' : Chart M r) : trAt x (c.map φ) (c'.map φ) = trAt x c c' := by
  unfold trAt
  rw [trS_map_iso]
  rfl

private theorem chart_ext {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U : X.Opens} {e e' : Fin r → Γ(M, U)}
    (he : IsFrame e) (he' : IsFrame e') (h : ∀ i, e i = e' i) : (⟨U, e, he⟩ : Chart M r) = ⟨U, e', he'⟩ := by
  obtain rfl : e = e' := funext h
  rfl

private theorem pull_comp {B Y T : Scheme.{0}} (π : Y ⟶ B) (g' : T ⟶ Y) {M : B.Modules} {r : ℕ} (hM : IsVB M r)
    (b : Chart M r) : b.pull hM (g' ≫ π) =
      ((b.pull hM π).pull (hM.pullback π) g').map ((Scheme.Modules.pullbackComp g' π).app M) :=
  chart_ext (U := (g' ≫ π) ⁻¹ᵁ b.U) _ _ fun i =>
    (PullPull.pullbackComp_hom_app g' π M le_rfl le_rfl le_rfl (b.e i)).symm

theorem UpperTheory.flag_connection_adapted :
    ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (M : ι → B.Modules) (n : ι → ℕ) (hM : ∀ a, IsVB (M a) (n a)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (M a)) (n a)), GlobalTheory.FlagConnect.Carries π M n fl g' g w fl' → ∀ (a : ι) (ch : Chart ((Scheme.Modules.pullback π).obj (M a)) (n a)), IsAdapted (fl a) ch → ∃ ch' : Chart ((Scheme.Modules.pullback g).obj (M a)) (n a), ch'.U = g' ⁻¹ᵁ ch.U ∧ IsAdapted (fl' a) ch' ∧ ∀ (K : Type) [CommRing K] (x : Sp K ⟶ T) (b : Chart (M a) (n a)), ⊤ ≤ (x ≫ g) ⁻¹ᵁ b.U → ⊤ ≤ (x ≫ g') ⁻¹ᵁ ch.U → trAt x (b.pull (hM a) g) ch' = trAt (x ≫ g') (b.pull (hM a) π) ch := by
  intro B Y T π ι M n hM fl g' g w fl' hC a ch had
  subst w
  have hP := (hM a).pullback π
  refine ⟨(ch.pull hP g').map ((Scheme.Modules.pullbackComp g' π).app (M a)), rfl, fun i => ?_,
    fun K _ x b hb hc => ?_⟩
  · obtain ⟨s, hs⟩ := had i
    obtain ⟨e, he⟩ := hC a i.succ
    simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at he
    refine ⟨e.hom.app (g' ⁻¹ᵁ ch.U) (QCoh.pullbackSections g' _ le_rfl s), ?_⟩
    refine (QCoh.app_app e.hom ((fl' a).ι i.succ) (g' ⁻¹ᵁ ch.U) _).trans ?_
    rw [he, ← QCoh.app_app, QCoh.pullback_map_app_pullbackSections, hs]
    rfl
  · have hb' : ⊤ ≤ (x ≫ g') ⁻¹ᵁ (b.pull (hM a) π).U := fun p hp => by
      have := hb hp
      rw [← Category.assoc] at this
      exact this
    rw [pull_comp, trAt_map_iso, trAt_pull hP g' _ _ hb' hc]
