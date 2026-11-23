import Development.WeilBound.CoreStatements.VolumeEquality.Pieces

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {Or : CptOrigin Y S₀ Dc Hd}
  {B : BaseUnif Y Or.sm Dc.j Dc.j' Dc.n} {FF : Fin B.np → Set (Fin Dc.n → ℂ)} {d : Fin B.np → ℕ} (Z : Sheets Or B FF d)

theorem Sheets.at (m : ℕ) (t : Fin Dc.n → ℂ) (ht : t ∈ Z.V m) : CoordsAt Or.𝔐.ξ Dc.y (Z.z m t) (Z.γ m t) ∧ Or.𝔐.Interior (Z.z m t) ∧
    Or.𝔐.LabVal (Z.z m t) Or.sm (B.F (Z.pc m)).σ := by
  have hi := (interior_iff Or.𝔐 _).1 (Z.z_over m t ht ▸ B.interior _ t (Z.V_sub m ht))
  refine ⟨Z.z_coords m t ht, hi, ?_⟩
  rw [funext (B.σ_eq (Z.pc m))]
  exact labVal_of_over Or.𝔐 hi (by rw [← Category.assoc, Z.z_over m t ht, B.comp_s_eq_spMap_of_isOver _ t (Z.V_sub m ht)]) _

def Sheets.pieces (hG : Top.Given) (hF : ∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) : Pieces Or where
  np := B.np
  g := B.g
  Λ k := (B.Di k).La
  F := B.F
  Γ := B.Γ
  arith := B.arith
  FF := FF
  fund := hF
  d := d
  d_pos := Z.d_pos
  pc := Z.pc
  V := Z.V
  B := Z.Bm
  γ := Z.γ
  cover := Z.cover
  V_sub := Z.V_sub
  B_sub := Z.B_sub
  count := Z.count
  fibre m t ht := ⟨Z.z m t, (Z.at m t ht).1, (Z.at m t ht).2.1,
    ((GlobalTheory.T.fibre_lattice_base_change_conj E H _ _ Y.t Or.𝔐.t Or.𝔐.f _ _ ((B.F _).R t) ((B.F _).R t) _).1 ⟨Or.𝔐.m⟩).2
      (Z.z_over m t ht ▸ B.lat _ t (Z.V_sub m ht)), (Z.at m t ht).2.2⟩
  pot m := GlobalTheory.T.cusp_volume_limit hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or _ _ (B.F (Z.pc m)) (Z.V m) (Z.z m) (Z.γ m) (Z.cover.isOpen m)
    (Z.V_sub m) (Z.cover.hol m) (Z.at m) (B.vec S₀ Ω K J Dc.y Or.𝔐 _ _ _ (Z.cover.isOpen m) (Z.V_sub m)
      (GlobalTheory.T.holomorphic_coords_of_generic_point _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie Or.𝔐.all _ _ _ _ (Z.cover.isOpen m) (Z.cover.hol m) (Z.z_coords m)) (Z.z_over m))

variable (Or) in
theorem exists_base (h : BaseUnifEx) (hG : Top.Given) : ∃ (B : BaseUnif Y Or.sm Dc.j Dc.j' Dc.n) (FF : Fin B.np → Set (Fin Dc.n → ℂ)),
    ∀ k, (B.F k).IsFundSet (B.Γ k) (FF k) := by
  have hN := Or.N_eq
  obtain ⟨B⟩ := h hG E H D l (Xo l) c Y Or.sm Dc.j Dc.j' Dc.n (by have := Dc.two_le_N; omega)
    (Or.side.imp (fun h => ⟨h.2.1, h.2.2, by have := h.2.2; unfold ComponentData.j'; omega⟩)
      fun h => ⟨h.2.1, h.2.2, by have := h.2.2; unfold ComponentData.j'; omega⟩) rfl
  exact ⟨B, Classical.skolem.1 fun k => GlobalTheory.T.exists_fundamental_set E _ _ _ _ _ _ (B.F k) (GlobalTheory.T.exists_group_dictionary E _ _ _ _ _ _ H (B.F k)).some _ (B.arith k)⟩

variable (Or) in
theorem pieces_of (h1 : HolNull) (h2 : ChartMeets) (h3 : RootBranches) (h4 : CoverRoots) (h5 : LocInj) (h6 : BaseUnifEx)
    (hG : Top.Given) : Nonempty (Pieces Or) := by
  obtain ⟨B, FF, hF⟩ := exists_base Or h6 hG
  obtain ⟨U, -, -, ⟨Z⟩⟩ := exists_sheets Or B h1 h2 h3 h4 h5 FF hF
  exact ⟨Z.pieces hG hF⟩

end SheetDecomposition
