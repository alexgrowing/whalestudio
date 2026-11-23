import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.TriFrDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AutomorphicArithmetic.DivisorFrames.ExtendToInvertibleMatrix
import Development.AutomorphicArithmetic.DivisorFrames.SplitActionCoordinateSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegerActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

private theorem tangent_combination_coordinates_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X} {g m : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x e cf w)
    {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} {a : Fin m → Fin g → R}
    (ha : ∀ l, IsCombAtG t x e (a l) (u l)) {cf : Fin g → R} {w : Sp (DualNumber R) ⟶ t.G.left}
    (hw : IsCombAtG t x e cf w) (c : Fin m → R) : IsCombAtG t x u c w ↔ cf = ∑ l, c l • a l := by
  constructor
  · intro h
    exact (hb w (Guard.comb_tan he hw)).unique hw (Chart.comb_comb he ha h)
  · rintro rfl
    obtain ⟨w', -, hw'⟩ := Guard.exists_comb (fun l => Guard.comb_tan he (ha l)) c
    exact Guard.comb_unique he (Chart.comb_comb he ha hw') hw ▸ hw'

private theorem existsUnique_basis_coordinates {T : Type} [CommRing T] {g : ℕ} (B : Matrix (Fin g) (Fin g) T) (hB : IsUnit B.det)
    (cf : Fin g → T) : ∃! c : Fin g → T, cf = ∑ l, c l • B l := by
  have h1 : ∀ c : Fin g → T, ∑ l, c l • B l = B.vecMul c := fun c => by
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  simp only [h1]
  refine ⟨B⁻¹.vecMul cf, ?_, ?_⟩
  · show cf = _
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hB, Matrix.vecMul_one]
  · rintro c rfl
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hB, Matrix.vecMul_one]

private theorem span_eq_of_triangular_change {K : Type} [Field K] {g n : ℕ} (v A₀ : Fin n → Fin g → K) (hv : LinearIndependent K v)
    (T : Fin n → Fin n → K) (hT : ∀ i, v i = ∑ l, T i l • A₀ l) :
    Submodule.span K (Set.range v) = Submodule.span K (Set.range A₀) := by
  apply Submodule.eq_of_le_of_finrank_le
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [hT i]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  · rw [finrank_span_eq_card hv]
    exact finrank_range_le_card A₀

theorem UpperTheory.split_eigen_tangent_coordinates :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (s : X ⟶ Sp A) (S : Type) [Fintype S] (ε : S → (𝓞 E →+* A)) (τ : S) (R K : Type) [CommRing R] [Field K] (ι : R →+* K), Function.Injective ι → ∀ (x₀ : Sp R ⟶ X) (κ : A →+* R), x₀ ≫ s = spMap κ → GlobalTheory.VB.IsSplitBy (fun σ => (ι.comp κ).comp (ε σ)) → (∀ σ, σ ≠ τ → ∃ c, IsUnit (κ (ε τ c) - κ (ε σ c))) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), IsTanBasis t x₀ e → ∀ (n : ℕ) (u₀ : Fin n → (Sp (DualNumber K) ⟶ t.G.left)), (∀ (m : Fin n) (c : 𝓞 E), u₀ m ≫ (t.act.act c).left = spMap (epsMul (ι (κ (ε τ c)))) ≫ u₀ m) → (∀ w, IsTanAtG t (spMap ι ≫ x₀) w → (∀ c : 𝓞 E, w ≫ (t.act.act c).left = spMap (epsMul (ι (κ (ε τ c)))) ≫ w) → ∃ cf : Fin n → K, IsCombAtG t (spMap ι ≫ x₀) u₀ cf w) → ∀ (A₀ : Fin n → Fin g → K), (∀ l, IsCombAtG t (spMap ι ≫ x₀) (fun i => spMap (dualMap ι) ≫ e i) (A₀ l) (u₀ l)) → ∀ (v : Fin n → Fin g → R) (T : Fin n → Fin n → K), (∀ i, (fun j => ι (v i j)) = ∑ l, T i l • A₀ l) → (∃ s₀, IsUnit (minor v le_rfl s₀)) → ∃ w : Fin n → (Sp (DualNumber R) ⟶ t.G.left), (∀ m, IsCombAtG t x₀ e (v m) (w m)) ∧ GlobalTheory.TriFlag.IsLocFr t s (ε τ) x₀ w := by
  intro E _ _ _ H X t A _ s S _ ε τ R K _ _ ι hι x₀ κ hκ hsp hun g e he n u₀ hu₀ hu₀s A₀ hA₀ v T hT ⟨s₀, hs₀⟩
  classical
  have : Nontrivial R := ι.domain_nontrivial
  obtain ⟨e', B, hB, hBv⟩ := UpperTheory.extend_to_invertible_matrix R n g v s₀ hs₀
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.tangent_basis_integer_action E H X t R x₀ g e he
  have hb : ∀ {T : Type} [CommRing T] (ψ : R →+* T) (i : Fin g),
      IsTanAtG t (spMap ψ ≫ x₀) (spMap (dualMap ψ) ≫ e i) := fun ψ i => GlobalTheory.LieMet.isTan_map ψ rfl (he.1 i)
  have hBm : ∀ {T : Type} [CommRing T] (ψ : R →+* T), IsUnit (B.map ψ).det := fun ψ => by
    have := hB.map ψ
    rwa [RingHom.map_det] at this
  choose u hut hu using fun i => Guard.exists_comb he.1 (B i)
  have hum : ∀ {T : Type} [CommRing T] (ψ : R →+* T) (i : Fin g),
      IsCombAtG t (spMap ψ ≫ x₀) (fun i => spMap (dualMap ψ) ≫ e i) (fun j => ψ (B i j)) (spMap (dualMap ψ) ≫ u i) :=
    fun ψ i => GlobalTheory.LatDRFree.comb_map t ψ (hu i)
  have heig : ∀ {T : Type} [CommRing T] (ψ : R →+* T) (cf : Fin g → T) w,
      IsCombAtG t (spMap ψ ≫ x₀) (fun i => spMap (dualMap ψ) ≫ e i) cf w → ∀ (c : 𝓞 E) (a : T),
      (w ≫ (t.act.act c).left = spMap (epsMul a) ≫ w ↔ ((ρ c).map ψ).mulVec cf = a • cf) := by
    intro T _ ψ cf w hw c a
    have h1 := hρ T ψ c cf w hw
    have h2 := Guard.comb_smul (hb ψ) hw a
    constructor
    · intro hE
      rw [← hE] at h2
      exact (he.2 T ψ _ (Guard.comb_tan (hb ψ) h1)).unique h1 h2
    · intro h
      rw [h] at h1
      exact Guard.comb_unique (hb ψ) h1 h2
  have hli : LinearIndependent K fun m j => ι (v m j) := by
    have h1 : LinearIndependent K (B.map ι).row :=
      Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (hBm ι))
    have h2 := h1.comp e' e'.injective
    convert h2 using 1
    funext m j
    simp [← hBv]
  have hK : ∀ cf : Fin g → K, (∀ c, ((ρ c).map ι).mulVec cf = ι (κ (ε τ c)) • cf) ↔
      cf ∈ Submodule.span K (Set.range fun m j => ι (v m j)) := by
    intro cf
    rw [span_eq_of_triangular_change _ A₀ hli T hT]
    constructor
    · intro h
      obtain ⟨w, hwt, hw⟩ := Guard.exists_comb (hb ι) cf
      obtain ⟨c, hc⟩ := hu₀s w hwt fun c => (heig ι cf w hw c _).2 (h c)
      rw [(tangent_combination_coordinates_iff (hb ι) (he.2 K ι) hA₀ hw c).1 hc]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    · intro h c
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 h
      rw [Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mulVec_smul, (heig ι _ _ (hA₀ l) c _).1 (hu₀ l c), smul_comm]
  have main := UpperTheory.split_action_coordinate_span (𝓞 E) R K S ι hι g n ρ (fun σ => κ.comp (ε σ)) τ hsp hun v e' B hB hBv hK
  refine ⟨fun m => u (e' m), fun m => hBv m ▸ hu (e' m), ⟨g, e', u, fun _ => rfl, hut, ?_⟩, ?_⟩
  · intro T _ φ w hw
    obtain ⟨cf, hcf, -⟩ := he.2 T φ w hw
    simp only [tangent_combination_coordinates_iff (hb φ) (he.2 T φ) (hum φ) hcf]
    exact existsUnique_basis_coordinates (B.map φ) (hBm φ) cf
  · intro R' _ α ψ hψ
    obtain rfl : ψ = α.comp κ := by
      apply GlobalTheory.ShFam.EigLoc.spMap_inj
      rw [← hψ, Category.assoc, hκ]
      exact (Spec.map_comp _ _).symm
    obtain ⟨m1, m2⟩ := main R' α
    have hwm : ∀ m, IsCombAtG t (spMap α ≫ x₀) (fun i => spMap (dualMap α) ≫ e i) (fun j => α (v m j))
        (spMap (dualMap α) ≫ u (e' m)) := fun m => hBv m ▸ hum α (e' m)
    refine ⟨fun m c => (heig α _ _ (hwm m) c _).2 (m1 m c), fun w' hw' hE => ?_⟩
    obtain ⟨cf, hcf, -⟩ := he.2 R' α w' hw'
    simp only [tangent_combination_coordinates_iff (hb α) (he.2 R' α) hwm hcf]
    exact m2 cf fun c => (heig α cf w' hcf c _).1 (hE c)
